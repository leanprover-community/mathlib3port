/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston

! This file was ported from Lean 3 source module representation_theory.group_cohomology_resolution
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.ModuleCat.Projective
import Mathbin.AlgebraicTopology.ExtraDegeneracy
import Mathbin.CategoryTheory.Abelian.Ext
import Mathbin.RepresentationTheory.RepCat

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains facts about an important `k[G]`-module structure on `k[Gⁿ]`, where `k` is a
commutative ring and `G` is a group. The module structure arises from the representation
`G →* End(k[Gⁿ])` induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define an isomorphism of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

This allows us to define a `k[G]`-basis on `k[Gⁿ⁺¹]`, by mapping the natural `k[G]`-basis of
`k[G] ⊗ₖ k[Gⁿ]` along the isomorphism.

We then define the standard resolution of `k` as a trivial representation, by
taking the alternating face map complex associated to an appropriate simplicial `k`-linear
`G`-representation. This simplicial object is the `linearization` of the simplicial `G`-set given
by the universal cover of the classifying space of `G`, `EG`. We prove this simplicial `G`-set `EG`
is isomorphic to the Čech nerve of the natural arrow of `G`-sets `G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `group_cohomology.ProjectiveResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

## Main definitions

 * `group_cohomology.resolution.to_tensor`
 * `group_cohomology.resolution.of_tensor`
 * `Rep.of_mul_action`
 * `group_cohomology.resolution.equiv_tensor`
 * `group_cohomology.resolution.of_mul_action_basis`
 * `classifying_space_universal_cover`
 * `group_cohomology.resolution.forget₂_to_Module_homotopy_equiv`
 * `group_cohomology.ProjectiveResolution`

## Implementation notes

We express `k[G]`-module structures on a module `k`-module `V` using the `representation`
definition. We avoid using instances `module (G →₀ k) V` so that we do not run into possible
scalar action diamonds.

We also use the category theory library to bundle the type `k[Gⁿ]` - or more generally `k[H]` when
`H` has `G`-action - and the representation together, as a term of type `Rep k G`, and call it
`Rep.of_mul_action k G H.` This enables us to express the fact that certain maps are
`G`-equivariant by constructing morphisms in the category `Rep k G`, i.e., representations of `G`
over `k`.
-/


noncomputable section

universe u v w

variable {k G : Type u} [CommRing k] {n : ℕ}

open TensorProduct

open CategoryTheory

-- mathport name: «exprGⁿ»
local notation "Gⁿ" => Fin n → G

-- mathport name: «exprGⁿ⁺¹»
local notation "Gⁿ⁺¹" => Fin (n + 1) → G

namespace GroupCohomology.resolution

open Finsupp hiding lift

open Fin (partialProd)

open Representation

section Basis

variable (k G n) [Group G]

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def toTensorAux : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (G →₀ k) ⊗[k] ((Fin n → G) →₀ k) :=
  Finsupp.lift ((G →₀ k) ⊗[k] ((Fin n → G) →₀ k)) k (Fin (n + 1) → G) fun x =>
    single (x 0) 1 ⊗ₜ[k] single (fun i => (x i)⁻¹ * x i.succ) 1
#align group_cohomology.resolution.to_tensor_aux GroupCohomology.Resolution.toTensorAux

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def ofTensorAux : (G →₀ k) ⊗[k] ((Fin n → G) →₀ k) →ₗ[k] (Fin (n + 1) → G) →₀ k :=
  TensorProduct.lift
    ((Finsupp.lift _ _ _) fun g => Finsupp.lift _ _ _ fun f => single (g • partialProd f) (1 : k))
#align group_cohomology.resolution.of_tensor_aux GroupCohomology.Resolution.ofTensorAux

variable {k G n}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_tensor_aux_single [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")]
         []
         ")")
        (Term.explicitBinder "(" [`m] [":" `k] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `toTensorAux [`k `G `n (Term.app `single [`f `m])])
         "="
         (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
          (Term.app `single [(Term.app `f [(num "0")]) `m])
          " ⊗ₜ "
          (Term.app
           `single
           [(Term.fun
             "fun"
             (Term.basicFun
              [`i]
              []
              "=>"
              («term_*_»
               («term_⁻¹» (Term.app `f [`i]) "⁻¹")
               "*"
               (Term.app `f [(Term.proj `i "." `succ)]))))
            (num "1")])))))
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
             [(Tactic.simpLemma [] [] `to_tensor_aux)
              ","
              (Tactic.simpLemma [] [] `lift_apply)
              ","
              (Tactic.simpLemma [] [] `sum_single_index)
              ","
              (Tactic.simpLemma [] [] `TensorProduct.smul_tmul')]
             "]"]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] [])])])))
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
            [(Tactic.simpLemma [] [] `to_tensor_aux)
             ","
             (Tactic.simpLemma [] [] `lift_apply)
             ","
             (Tactic.simpLemma [] [] `sum_single_index)
             ","
             (Tactic.simpLemma [] [] `TensorProduct.smul_tmul')]
            "]"]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] [] [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `to_tensor_aux)
         ","
         (Tactic.simpLemma [] [] `lift_apply)
         ","
         (Tactic.simpLemma [] [] `sum_single_index)
         ","
         (Tactic.simpLemma [] [] `TensorProduct.smul_tmul')]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TensorProduct.smul_tmul'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sum_single_index
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lift_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_tensor_aux
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `toTensorAux [`k `G `n (Term.app `single [`f `m])])
       "="
       (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
        (Term.app `single [(Term.app `f [(num "0")]) `m])
        " ⊗ₜ "
        (Term.app
         `single
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            («term_*_»
             («term_⁻¹» (Term.app `f [`i]) "⁻¹")
             "*"
             (Term.app `f [(Term.proj `i "." `succ)]))))
          (num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
       (Term.app `single [(Term.app `f [(num "0")]) `m])
       " ⊗ₜ "
       (Term.app
        `single
        [(Term.fun
          "fun"
          (Term.basicFun
           [`i]
           []
           "=>"
           («term_*_»
            («term_⁻¹» (Term.app `f [`i]) "⁻¹")
            "*"
            (Term.app `f [(Term.proj `i "." `succ)]))))
         (num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `single
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          («term_*_»
           («term_⁻¹» (Term.app `f [`i]) "⁻¹")
           "*"
           (Term.app `f [(Term.proj `i "." `succ)]))))
        (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        («term_*_»
         («term_⁻¹» (Term.app `f [`i]) "⁻¹")
         "*"
         (Term.app `f [(Term.proj `i "." `succ)]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_⁻¹» (Term.app `f [`i]) "⁻¹") "*" (Term.app `f [(Term.proj `i "." `succ)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.proj `i "." `succ)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `i "." `succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_⁻¹» (Term.app `f [`i]) "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`i]) ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`i]
       []
       "=>"
       («term_*_»
        («term_⁻¹» (Term.paren "(" (Term.app `f [`i]) ")") "⁻¹")
        "*"
        (Term.app `f [(Term.proj `i "." `succ)]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app `single [(Term.app `f [(num "0")]) `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [(num "0")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 101, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `toTensorAux [`k `G `n (Term.app `single [`f `m])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [`f `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `single [`f `m]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `toTensorAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ⁺¹._@.RepresentationTheory.GroupCohomologyResolution._hyg.43'
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
  to_tensor_aux_single
  ( f : Gⁿ⁺¹ ) ( m : k )
    : toTensorAux k G n single f m = single f 0 m ⊗ₜ single fun i => f i ⁻¹ * f i . succ 1
  :=
    by simp only [ to_tensor_aux , lift_apply , sum_single_index , TensorProduct.smul_tmul' ] · simp
#align
  group_cohomology.resolution.to_tensor_aux_single GroupCohomology.Resolution.to_tensor_aux_single

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_tensor_aux_of_mul_action [])
      (Command.declSig
       [(Term.explicitBinder "(" [`g] [":" `G] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `toTensorAux
          [`k
           `G
           `n
           (Term.app
            `ofMulAction
            [`k
             `G
             (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
             `g
             (Term.app `single [`x (num "1")])])])
         "="
         (Term.app
          `TensorProduct.map
          [(Term.app `ofMulAction [`k `G `G `g])
           (num "1")
           (Term.app `toTensorAux [`k `G `n (Term.app `single [`x (num "1")])])]))))
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
            ["["
             [(Tactic.simpLemma [] [] `of_mul_action_def)
              ","
              (Tactic.simpLemma [] [] `to_tensor_aux_single)
              ","
              (Tactic.simpLemma [] [] `mul_assoc)
              ","
              (Tactic.simpLemma [] [] `inv_mul_cancel_left)]
             "]"]
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
           ["["
            [(Tactic.simpLemma [] [] `of_mul_action_def)
             ","
             (Tactic.simpLemma [] [] `to_tensor_aux_single)
             ","
             (Tactic.simpLemma [] [] `mul_assoc)
             ","
             (Tactic.simpLemma [] [] `inv_mul_cancel_left)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `of_mul_action_def)
         ","
         (Tactic.simpLemma [] [] `to_tensor_aux_single)
         ","
         (Tactic.simpLemma [] [] `mul_assoc)
         ","
         (Tactic.simpLemma [] [] `inv_mul_cancel_left)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_mul_cancel_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_tensor_aux_single
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_mul_action_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `toTensorAux
        [`k
         `G
         `n
         (Term.app
          `ofMulAction
          [`k
           `G
           (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
           `g
           (Term.app `single [`x (num "1")])])])
       "="
       (Term.app
        `TensorProduct.map
        [(Term.app `ofMulAction [`k `G `G `g])
         (num "1")
         (Term.app `toTensorAux [`k `G `n (Term.app `single [`x (num "1")])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `TensorProduct.map
       [(Term.app `ofMulAction [`k `G `G `g])
        (num "1")
        (Term.app `toTensorAux [`k `G `n (Term.app `single [`x (num "1")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `toTensorAux [`k `G `n (Term.app `single [`x (num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [`x (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `single [`x (num "1")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `toTensorAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `toTensorAux [`k `G `n (Term.paren "(" (Term.app `single [`x (num "1")]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ofMulAction [`k `G `G `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ofMulAction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ofMulAction [`k `G `G `g])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TensorProduct.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `toTensorAux
       [`k
        `G
        `n
        (Term.app
         `ofMulAction
         [`k
          `G
          (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
          `g
          (Term.app `single [`x (num "1")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ofMulAction
       [`k
        `G
        (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
        `g
        (Term.app `single [`x (num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [`x (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `single [`x (num "1")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ⁺¹._@.RepresentationTheory.GroupCohomologyResolution._hyg.43'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  to_tensor_aux_of_mul_action
  ( g : G ) ( x : Gⁿ⁺¹ )
    :
      toTensorAux k G n ofMulAction k G Gⁿ⁺¹ g single x 1
        =
        TensorProduct.map ofMulAction k G G g 1 toTensorAux k G n single x 1
  := by simp [ of_mul_action_def , to_tensor_aux_single , mul_assoc , inv_mul_cancel_left ]
#align
  group_cohomology.resolution.to_tensor_aux_of_mul_action GroupCohomology.Resolution.to_tensor_aux_of_mul_action

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `of_tensor_aux_single [])
      (Command.declSig
       [(Term.explicitBinder "(" [`g] [":" `G] [] ")")
        (Term.explicitBinder "(" [`m] [":" `k] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":"
          (Data.Finsupp.Defs.«term_→₀_»
           (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
           " →₀ "
           `k)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `ofTensorAux
          [`k
           `G
           `n
           (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
            (Term.app `single [`g `m])
            " ⊗ₜ "
            `x)])
         "="
         (Term.app
          `Finsupp.lift
          [(Data.Finsupp.Defs.«term_→₀_»
            (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
            " →₀ "
            `k)
           `k
           (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
           (Term.fun
            "fun"
            (Term.basicFun
             [`f]
             []
             "=>"
             (Term.app
              `single
              [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])))
           `x]))))
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
            ["["
             [(Tactic.simpLemma [] [] `of_tensor_aux)
              ","
              (Tactic.simpLemma [] [] `sum_single_index)
              ","
              (Tactic.simpLemma [] [] `smul_sum)
              ","
              (Tactic.simpLemma [] [] (Term.app `mul_comm [`m]))]
             "]"]
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
           ["["
            [(Tactic.simpLemma [] [] `of_tensor_aux)
             ","
             (Tactic.simpLemma [] [] `sum_single_index)
             ","
             (Tactic.simpLemma [] [] `smul_sum)
             ","
             (Tactic.simpLemma [] [] (Term.app `mul_comm [`m]))]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `of_tensor_aux)
         ","
         (Tactic.simpLemma [] [] `sum_single_index)
         ","
         (Tactic.simpLemma [] [] `smul_sum)
         ","
         (Tactic.simpLemma [] [] (Term.app `mul_comm [`m]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [`m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sum_single_index
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_tensor_aux
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `ofTensorAux
        [`k
         `G
         `n
         (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
          (Term.app `single [`g `m])
          " ⊗ₜ "
          `x)])
       "="
       (Term.app
        `Finsupp.lift
        [(Data.Finsupp.Defs.«term_→₀_»
          (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
          " →₀ "
          `k)
         `k
         (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
         (Term.fun
          "fun"
          (Term.basicFun
           [`f]
           []
           "=>"
           (Term.app
            `single
            [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])))
         `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finsupp.lift
       [(Data.Finsupp.Defs.«term_→₀_»
         (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
         " →₀ "
         `k)
        `k
        (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
        (Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
          (Term.app
           `single
           [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])))
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
        [`f]
        []
        "=>"
        (Term.app
         `single
         [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `partialProd [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `partialProd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`f]
       []
       "=>"
       (Term.app
        `single
        [(Term.paren "(" (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) ")")
         `m])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ._@.RepresentationTheory.GroupCohomologyResolution._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  of_tensor_aux_single
  ( g : G ) ( m : k ) ( x : Gⁿ →₀ k )
    :
      ofTensorAux k G n single g m ⊗ₜ x
        =
        Finsupp.lift Gⁿ⁺¹ →₀ k k Gⁿ fun f => single g • partialProd f m x
  := by simp [ of_tensor_aux , sum_single_index , smul_sum , mul_comm m ]
#align
  group_cohomology.resolution.of_tensor_aux_single GroupCohomology.Resolution.of_tensor_aux_single

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `of_tensor_aux_comm_of_mul_action [])
      (Command.declSig
       [(Term.explicitBinder "(" [`g `h] [":" `G] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `ofTensorAux
          [`k
           `G
           `n
           (Term.app
            `TensorProduct.map
            [(Term.app `ofMulAction [`k `G `G `g])
             (Term.typeAscription
              "("
              (num "1")
              ":"
              [(Term.app
                `Module.EndCat
                [`k
                 (Data.Finsupp.Defs.«term_→₀_»
                  (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
                  " →₀ "
                  `k)])]
              ")")
             (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
              (Term.app `single [`h (Term.typeAscription "(" (num "1") ":" [`k] ")")])
              " ⊗ₜ "
              (Term.app `single [`x (Term.typeAscription "(" (num "1") ":" [`k] ")")]))])])
         "="
         (Term.app
          `ofMulAction
          [`k
           `G
           (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
           `g
           (Term.app
            `ofTensorAux
            [`k
             `G
             `n
             (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
              (Term.app `single [`h (num "1")])
              " ⊗ₜ "
              (Term.app `single [`x (num "1")]))])]))))
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
            ["["
             [(Tactic.simpLemma [] [] `of_mul_action_def)
              ","
              (Tactic.simpLemma [] [] `of_tensor_aux_single)
              ","
              (Tactic.simpLemma [] [] `mul_smul)]
             "]"]
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
           ["["
            [(Tactic.simpLemma [] [] `of_mul_action_def)
             ","
             (Tactic.simpLemma [] [] `of_tensor_aux_single)
             ","
             (Tactic.simpLemma [] [] `mul_smul)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `of_mul_action_def)
         ","
         (Tactic.simpLemma [] [] `of_tensor_aux_single)
         ","
         (Tactic.simpLemma [] [] `mul_smul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_tensor_aux_single
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_mul_action_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `ofTensorAux
        [`k
         `G
         `n
         (Term.app
          `TensorProduct.map
          [(Term.app `ofMulAction [`k `G `G `g])
           (Term.typeAscription
            "("
            (num "1")
            ":"
            [(Term.app
              `Module.EndCat
              [`k
               (Data.Finsupp.Defs.«term_→₀_»
                (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
                " →₀ "
                `k)])]
            ")")
           (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
            (Term.app `single [`h (Term.typeAscription "(" (num "1") ":" [`k] ")")])
            " ⊗ₜ "
            (Term.app `single [`x (Term.typeAscription "(" (num "1") ":" [`k] ")")]))])])
       "="
       (Term.app
        `ofMulAction
        [`k
         `G
         (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
         `g
         (Term.app
          `ofTensorAux
          [`k
           `G
           `n
           (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
            (Term.app `single [`h (num "1")])
            " ⊗ₜ "
            (Term.app `single [`x (num "1")]))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ofMulAction
       [`k
        `G
        (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
        `g
        (Term.app
         `ofTensorAux
         [`k
          `G
          `n
          (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
           (Term.app `single [`h (num "1")])
           " ⊗ₜ "
           (Term.app `single [`x (num "1")]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ofTensorAux
       [`k
        `G
        `n
        (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
         (Term.app `single [`h (num "1")])
         " ⊗ₜ "
         (Term.app `single [`x (num "1")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
       (Term.app `single [`h (num "1")])
       " ⊗ₜ "
       (Term.app `single [`x (num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [`x (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app `single [`h (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 100, (some 101,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
      (Term.app `single [`h (num "1")])
      " ⊗ₜ "
      (Term.app `single [`x (num "1")]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ofTensorAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `ofTensorAux
      [`k
       `G
       `n
       (Term.paren
        "("
        (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
         (Term.app `single [`h (num "1")])
         " ⊗ₜ "
         (Term.app `single [`x (num "1")]))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ⁺¹._@.RepresentationTheory.GroupCohomologyResolution._hyg.43'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  of_tensor_aux_comm_of_mul_action
  ( g h : G ) ( x : Gⁿ )
    :
      ofTensorAux
          k
            G
            n
            TensorProduct.map
              ofMulAction k G G g
                ( 1 : Module.EndCat k Gⁿ →₀ k )
                single h ( 1 : k ) ⊗ₜ single x ( 1 : k )
        =
        ofMulAction k G Gⁿ⁺¹ g ofTensorAux k G n single h 1 ⊗ₜ single x 1
  := by simp [ of_mul_action_def , of_tensor_aux_single , mul_smul ]
#align
  group_cohomology.resolution.of_tensor_aux_comm_of_mul_action GroupCohomology.Resolution.of_tensor_aux_comm_of_mul_action

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_tensor_aux_left_inv [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":"
          (Data.Finsupp.Defs.«term_→₀_»
           (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
           " →₀ "
           `k)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `ofTensorAux
          [(Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.app `toTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])])
         "="
         `x)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj `LinearMap.ext_iff "." (fieldIdx "1"))
             [(Term.app
               (Term.explicit "@" `Finsupp.lhom_ext)
               [(Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                `k
                (Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.app
                 `LinearMap.comp
                 [(Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                  (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                `LinearMap.id
                (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.hole "_")))])
              `x]))
           []
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `to_tensor_aux_single [`x `y]))
              ","
              (Tactic.rwRule [] `of_tensor_aux_single)
              ","
              (Tactic.rwRule [] `Finsupp.lift_apply)
              ","
              (Tactic.rwRule [] `Finsupp.sum_single_index)
              ","
              (Tactic.rwRule [] `one_smul)
              ","
              (Tactic.rwRule [] `Fin.partial_prod_left_inv)]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_smul)] "]")
              [])])])))
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
            (Term.proj `LinearMap.ext_iff "." (fieldIdx "1"))
            [(Term.app
              (Term.explicit "@" `Finsupp.lhom_ext)
              [(Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               `k
               (Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.app
                `LinearMap.comp
                [(Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                 (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
               `LinearMap.id
               (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.hole "_")))])
             `x]))
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `to_tensor_aux_single [`x `y]))
             ","
             (Tactic.rwRule [] `of_tensor_aux_single)
             ","
             (Tactic.rwRule [] `Finsupp.lift_apply)
             ","
             (Tactic.rwRule [] `Finsupp.sum_single_index)
             ","
             (Tactic.rwRule [] `one_smul)
             ","
             (Tactic.rwRule [] `Fin.partial_prod_left_inv)]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_smul)] "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_smul)] "]") [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_smul)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `to_tensor_aux_single [`x `y]))
         ","
         (Tactic.rwRule [] `of_tensor_aux_single)
         ","
         (Tactic.rwRule [] `Finsupp.lift_apply)
         ","
         (Tactic.rwRule [] `Finsupp.sum_single_index)
         ","
         (Tactic.rwRule [] `one_smul)
         ","
         (Tactic.rwRule [] `Fin.partial_prod_left_inv)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.partial_prod_left_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.sum_single_index
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.lift_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_tensor_aux_single
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_tensor_aux_single [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_tensor_aux_single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj `LinearMap.ext_iff "." (fieldIdx "1"))
        [(Term.app
          (Term.explicit "@" `Finsupp.lhom_ext)
          [(Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           `k
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.app
            `LinearMap.comp
            [(Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
             (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
           `LinearMap.id
           (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.hole "_")))])
         `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `LinearMap.ext_iff "." (fieldIdx "1"))
       [(Term.app
         (Term.explicit "@" `Finsupp.lhom_ext)
         [(Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          `k
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.app
           `LinearMap.comp
           [(Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
            (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
          `LinearMap.id
          (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.hole "_")))])
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.explicit "@" `Finsupp.lhom_ext)
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        `k
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.app
         `LinearMap.comp
         [(Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
          (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
        `LinearMap.id
        (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `LinearMap.id
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `LinearMap.comp
       [(Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_tensor_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of_tensor_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearMap.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `LinearMap.comp
      [(Term.paren
        "("
        (Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        ")")
       (Term.paren
        "("
        (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        ")")])
     ")")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Finsupp.lhom_ext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.lhom_ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.explicit "@" `Finsupp.lhom_ext)
      [(Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       `k
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.paren
        "("
        (Term.app
         `LinearMap.comp
         [(Term.paren
           "("
           (Term.app `of_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
           ")")
          (Term.paren
           "("
           (Term.app `to_tensor_aux [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
           ")")])
        ")")
       `LinearMap.id
       (Term.fun "fun" (Term.basicFun [`x `y] [] "=>" (Term.hole "_")))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `LinearMap.ext_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `LinearMap.ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `ofTensorAux
        [(Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.app `toTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])])
       "="
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `ofTensorAux
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.app `toTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `toTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `toTensorAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `toTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
     ")")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ofTensorAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Finsupp.Defs.«term_→₀_»
       (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
       " →₀ "
       `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ⁺¹._@.RepresentationTheory.GroupCohomologyResolution._hyg.43'
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
  to_tensor_aux_left_inv
  ( x : Gⁿ⁺¹ →₀ k ) : ofTensorAux _ _ _ toTensorAux _ _ _ x = x
  :=
    by
      refine'
          LinearMap.ext_iff . 1
            @ Finsupp.lhom_ext
                _
                  _
                  _
                  k
                  _
                  _
                  _
                  _
                  _
                  LinearMap.comp of_tensor_aux _ _ _ to_tensor_aux _ _ _
                  LinearMap.id
                  fun x y => _
              x
        dsimp
        rw
          [
            to_tensor_aux_single x y
              ,
              of_tensor_aux_single
              ,
              Finsupp.lift_apply
              ,
              Finsupp.sum_single_index
              ,
              one_smul
              ,
              Fin.partial_prod_left_inv
            ]
        · rw [ zero_smul ]
#align
  group_cohomology.resolution.to_tensor_aux_left_inv GroupCohomology.Resolution.to_tensor_aux_left_inv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `to_tensor_aux_right_inv [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":"
          (TensorProduct.LinearAlgebra.TensorProduct.tensor_product
           (Data.Finsupp.Defs.«term_→₀_» `G " →₀ " `k)
           " ⊗["
           `k
           "] "
           (Data.Finsupp.Defs.«term_→₀_»
            (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
            " →₀ "
            `k))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `toTensorAux
          [(Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.app `ofTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])])
         "="
         `x)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `TensorProduct.induction_on
             [`x
              (Term.byTactic
               "by"
               (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
              (Term.fun "fun" (Term.basicFun [`y `z] [] "=>" (Term.hole "_")))
              (Term.fun
               "fun"
               (Term.basicFun
                [`z `w `hz `hw]
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
                     ["[" [(Tactic.simpLemma [] [] `hz) "," (Tactic.simpLemma [] [] `hw)] "]"]
                     [])])))))]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Finsupp.sum_single [`y]))
              ","
              (Tactic.rwRule [] `Finsupp.sum)
              ","
              (Tactic.rwRule [] `TensorProduct.sum_tmul)]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Finset.smul_sum)
              ","
              (Tactic.simpLemma [] [] `LinearMap.map_sum)]
             "]"]
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `Finset.sum_congr
             [`rfl (Term.fun "fun" (Term.basicFun [`f `hf] [] "=>" (Term.hole "_")))]))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `of_tensor_aux_single)
              ","
              (Tactic.simpLemma [] [] `Finsupp.lift_apply)
              ","
              (Tactic.simpLemma [] [] `Finsupp.smul_single')
              ","
              (Tactic.simpLemma [] [] `LinearMap.map_finsupp_sum)
              ","
              (Tactic.simpLemma [] [] `to_tensor_aux_single)
              ","
              (Tactic.simpLemma [] [] `Fin.partial_prod_right_inv)]
             "]"]
            [])
           []
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Fin.partial_prod_zero) "," (Tactic.simpLemma [] [] `mul_one)]
             "]"]
            [])
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
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `Finsupp.sum_single [`z]))
                  ","
                  (Tactic.rwRule [] `Finsupp.sum)
                  ","
                  (Tactic.rwRule [] `TensorProduct.tmul_sum)]
                 "]"))])))
           []
           (Tactic.exact
            "exact"
            (Term.app
             `Finset.sum_congr
             [`rfl
              (Term.fun
               "fun"
               (Term.basicFun
                [`g `hg]
                []
                "=>"
                (Term.show
                 "show"
                 («term_=_»
                  (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
                   (Term.hole "_")
                   " ⊗ₜ "
                   (Term.hole "_"))
                  "="
                  (Term.hole "_"))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finsupp.smul_single')
                        ","
                        (Tactic.rwRule [] `TensorProduct.smul_tmul)
                        ","
                        (Tactic.rwRule [] `Finsupp.smul_single_one)]
                       "]")
                      [])]))))))]))])))
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
            `TensorProduct.induction_on
            [`x
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
             (Term.fun "fun" (Term.basicFun [`y `z] [] "=>" (Term.hole "_")))
             (Term.fun
              "fun"
              (Term.basicFun
               [`z `w `hz `hw]
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
                    ["[" [(Tactic.simpLemma [] [] `hz) "," (Tactic.simpLemma [] [] `hw)] "]"]
                    [])])))))]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Finsupp.sum_single [`y]))
             ","
             (Tactic.rwRule [] `Finsupp.sum)
             ","
             (Tactic.rwRule [] `TensorProduct.sum_tmul)]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Finset.smul_sum)
             ","
             (Tactic.simpLemma [] [] `LinearMap.map_sum)]
            "]"]
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `Finset.sum_congr
            [`rfl (Term.fun "fun" (Term.basicFun [`f `hf] [] "=>" (Term.hole "_")))]))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `of_tensor_aux_single)
             ","
             (Tactic.simpLemma [] [] `Finsupp.lift_apply)
             ","
             (Tactic.simpLemma [] [] `Finsupp.smul_single')
             ","
             (Tactic.simpLemma [] [] `LinearMap.map_finsupp_sum)
             ","
             (Tactic.simpLemma [] [] `to_tensor_aux_single)
             ","
             (Tactic.simpLemma [] [] `Fin.partial_prod_right_inv)]
            "]"]
           [])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Fin.partial_prod_zero) "," (Tactic.simpLemma [] [] `mul_one)]
            "]"]
           [])
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
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `Finsupp.sum_single [`z]))
                 ","
                 (Tactic.rwRule [] `Finsupp.sum)
                 ","
                 (Tactic.rwRule [] `TensorProduct.tmul_sum)]
                "]"))])))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `Finset.sum_congr
            [`rfl
             (Term.fun
              "fun"
              (Term.basicFun
               [`g `hg]
               []
               "=>"
               (Term.show
                "show"
                («term_=_»
                 (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
                  (Term.hole "_")
                  " ⊗ₜ "
                  (Term.hole "_"))
                 "="
                 (Term.hole "_"))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finsupp.smul_single')
                       ","
                       (Tactic.rwRule [] `TensorProduct.smul_tmul)
                       ","
                       (Tactic.rwRule [] `Finsupp.smul_single_one)]
                      "]")
                     [])]))))))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Finset.sum_congr
        [`rfl
         (Term.fun
          "fun"
          (Term.basicFun
           [`g `hg]
           []
           "=>"
           (Term.show
            "show"
            («term_=_»
             (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
              (Term.hole "_")
              " ⊗ₜ "
              (Term.hole "_"))
             "="
             (Term.hole "_"))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finsupp.smul_single')
                   ","
                   (Tactic.rwRule [] `TensorProduct.smul_tmul)
                   ","
                   (Tactic.rwRule [] `Finsupp.smul_single_one)]
                  "]")
                 [])]))))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finset.sum_congr
       [`rfl
        (Term.fun
         "fun"
         (Term.basicFun
          [`g `hg]
          []
          "=>"
          (Term.show
           "show"
           («term_=_»
            (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
             (Term.hole "_")
             " ⊗ₜ "
             (Term.hole "_"))
            "="
            (Term.hole "_"))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finsupp.smul_single')
                  ","
                  (Tactic.rwRule [] `TensorProduct.smul_tmul)
                  ","
                  (Tactic.rwRule [] `Finsupp.smul_single_one)]
                 "]")
                [])]))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g `hg]
        []
        "=>"
        (Term.show
         "show"
         («term_=_»
          (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
           (Term.hole "_")
           " ⊗ₜ "
           (Term.hole "_"))
          "="
          (Term.hole "_"))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finsupp.smul_single')
                ","
                (Tactic.rwRule [] `TensorProduct.smul_tmul)
                ","
                (Tactic.rwRule [] `Finsupp.smul_single_one)]
               "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
         (Term.hole "_")
         " ⊗ₜ "
         (Term.hole "_"))
        "="
        (Term.hole "_"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finsupp.smul_single')
              ","
              (Tactic.rwRule [] `TensorProduct.smul_tmul)
              ","
              (Tactic.rwRule [] `Finsupp.smul_single_one)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finsupp.smul_single')
         ","
         (Tactic.rwRule [] `TensorProduct.smul_tmul)
         ","
         (Tactic.rwRule [] `Finsupp.smul_single_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.smul_single_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TensorProduct.smul_tmul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.smul_single'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_» (Term.hole "_") " ⊗ₜ " (Term.hole "_"))
       "="
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_» (Term.hole "_") " ⊗ₜ " (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 101, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.sum_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Finsupp.sum_single [`z]))
             ","
             (Tactic.rwRule [] `Finsupp.sum)
             ","
             (Tactic.rwRule [] `TensorProduct.tmul_sum)]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TensorProduct.tmul_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Finsupp.sum_single [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finsupp.sum_single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Fin.partial_prod_zero) "," (Tactic.simpLemma [] [] `mul_one)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.partial_prod_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `of_tensor_aux_single)
         ","
         (Tactic.simpLemma [] [] `Finsupp.lift_apply)
         ","
         (Tactic.simpLemma [] [] `Finsupp.smul_single')
         ","
         (Tactic.simpLemma [] [] `LinearMap.map_finsupp_sum)
         ","
         (Tactic.simpLemma [] [] `to_tensor_aux_single)
         ","
         (Tactic.simpLemma [] [] `Fin.partial_prod_right_inv)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.partial_prod_right_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_tensor_aux_single
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.map_finsupp_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.smul_single'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.lift_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_tensor_aux_single
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Finset.sum_congr
        [`rfl (Term.fun "fun" (Term.basicFun [`f `hf] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finset.sum_congr
       [`rfl (Term.fun "fun" (Term.basicFun [`f `hf] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`f `hf] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finset.sum_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Finset.smul_sum) "," (Tactic.simpLemma [] [] `LinearMap.map_sum)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.map_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.smul_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Finsupp.sum_single [`y]))
         ","
         (Tactic.rwRule [] `Finsupp.sum)
         ","
         (Tactic.rwRule [] `TensorProduct.sum_tmul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TensorProduct.sum_tmul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finsupp.sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Finsupp.sum_single [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finsupp.sum_single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `TensorProduct.induction_on
        [`x
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
         (Term.fun "fun" (Term.basicFun [`y `z] [] "=>" (Term.hole "_")))
         (Term.fun
          "fun"
          (Term.basicFun
           [`z `w `hz `hw]
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
                ["[" [(Tactic.simpLemma [] [] `hz) "," (Tactic.simpLemma [] [] `hw)] "]"]
                [])])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `TensorProduct.induction_on
       [`x
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
        (Term.fun "fun" (Term.basicFun [`y `z] [] "=>" (Term.hole "_")))
        (Term.fun
         "fun"
         (Term.basicFun
          [`z `w `hz `hw]
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
               ["[" [(Tactic.simpLemma [] [] `hz) "," (Tactic.simpLemma [] [] `hw)] "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`z `w `hz `hw]
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
             ["[" [(Tactic.simpLemma [] [] `hz) "," (Tactic.simpLemma [] [] `hw)] "]"]
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
           ["[" [(Tactic.simpLemma [] [] `hz) "," (Tactic.simpLemma [] [] `hw)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `hz) "," (Tactic.simpLemma [] [] `hw)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hw
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hw
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`y `z] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`y `z] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TensorProduct.induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `toTensorAux
        [(Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.app `ofTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])])
       "="
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `toTensorAux
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.app `ofTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ofTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ofTensorAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ofTensorAux [(Term.hole "_") (Term.hole "_") (Term.hole "_") `x])
     ")")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `toTensorAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TensorProduct.LinearAlgebra.TensorProduct.tensor_product
       (Data.Finsupp.Defs.«term_→₀_» `G " →₀ " `k)
       " ⊗["
       `k
       "] "
       (Data.Finsupp.Defs.«term_→₀_»
        (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
        " →₀ "
        `k))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Finsupp.Defs.«term_→₀_»
       (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
       " →₀ "
       `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ._@.RepresentationTheory.GroupCohomologyResolution._hyg.6'
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
  to_tensor_aux_right_inv
  ( x : G →₀ k ⊗[ k ] Gⁿ →₀ k ) : toTensorAux _ _ _ ofTensorAux _ _ _ x = x
  :=
    by
      refine' TensorProduct.induction_on x by simp fun y z => _ fun z w hz hw => by simp [ hz , hw ]
        rw [ ← Finsupp.sum_single y , Finsupp.sum , TensorProduct.sum_tmul ]
        simp only [ Finset.smul_sum , LinearMap.map_sum ]
        refine' Finset.sum_congr rfl fun f hf => _
        simp
          only
          [
            of_tensor_aux_single
              ,
              Finsupp.lift_apply
              ,
              Finsupp.smul_single'
              ,
              LinearMap.map_finsupp_sum
              ,
              to_tensor_aux_single
              ,
              Fin.partial_prod_right_inv
            ]
        dsimp
        simp only [ Fin.partial_prod_zero , mul_one ]
        conv_rhs => rw [ ← Finsupp.sum_single z , Finsupp.sum , TensorProduct.tmul_sum ]
        exact
          Finset.sum_congr
            rfl
              fun
                g hg
                  =>
                  show
                    _ ⊗ₜ _ = _
                    by
                      rw
                        [
                          ← Finsupp.smul_single' , TensorProduct.smul_tmul , Finsupp.smul_single_one
                          ]
#align
  group_cohomology.resolution.to_tensor_aux_right_inv GroupCohomology.Resolution.to_tensor_aux_right_inv

variable (k G n)

/-- A hom of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def toTensor :
    RepCat.ofMulAction k G (Fin (n + 1) → G) ⟶
      RepCat.of
        ((Representation.ofMulAction k G G).tprod (1 : G →* Module.EndCat k ((Fin n → G) →₀ k)))
    where
  hom := toTensorAux k G n
  comm' g := by ext <;> exact to_tensor_aux_of_mul_action _ _
#align group_cohomology.resolution.to_tensor GroupCohomology.Resolution.toTensor

/-- A hom of `k`-linear representations of `G` from `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)`. -/
def ofTensor :
    RepCat.of
        ((Representation.ofMulAction k G G).tprod (1 : G →* Module.EndCat k ((Fin n → G) →₀ k))) ⟶
      RepCat.ofMulAction k G (Fin (n + 1) → G)
    where
  hom := ofTensorAux k G n
  comm' g := by
    ext
    congr 1
    exact of_tensor_aux_comm_of_mul_action _ _ _
#align group_cohomology.resolution.of_tensor GroupCohomology.Resolution.ofTensor

variable {k G n}

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
      (Command.declId `to_tensor_single [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")]
         []
         ")")
        (Term.explicitBinder "(" [`m] [":" `k] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app `toTensor [`k `G `n]) "." `hom)
          [(Term.app `single [`f `m])])
         "="
         (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
          (Term.app `single [(Term.app `f [(num "0")]) `m])
          " ⊗ₜ "
          (Term.app
           `single
           [(Term.fun
             "fun"
             (Term.basicFun
              [`i]
              []
              "=>"
              («term_*_»
               («term_⁻¹» (Term.app `f [`i]) "⁻¹")
               "*"
               (Term.app `f [(Term.proj `i "." `succ)]))))
            (num "1")])))))
      (Command.declValSimple
       ":="
       (Term.app `to_tensor_aux_single [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_tensor_aux_single [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_tensor_aux_single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj (Term.app `toTensor [`k `G `n]) "." `hom) [(Term.app `single [`f `m])])
       "="
       (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
        (Term.app `single [(Term.app `f [(num "0")]) `m])
        " ⊗ₜ "
        (Term.app
         `single
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            («term_*_»
             («term_⁻¹» (Term.app `f [`i]) "⁻¹")
             "*"
             (Term.app `f [(Term.proj `i "." `succ)]))))
          (num "1")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
       (Term.app `single [(Term.app `f [(num "0")]) `m])
       " ⊗ₜ "
       (Term.app
        `single
        [(Term.fun
          "fun"
          (Term.basicFun
           [`i]
           []
           "=>"
           («term_*_»
            («term_⁻¹» (Term.app `f [`i]) "⁻¹")
            "*"
            (Term.app `f [(Term.proj `i "." `succ)]))))
         (num "1")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `single
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          («term_*_»
           («term_⁻¹» (Term.app `f [`i]) "⁻¹")
           "*"
           (Term.app `f [(Term.proj `i "." `succ)]))))
        (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        («term_*_»
         («term_⁻¹» (Term.app `f [`i]) "⁻¹")
         "*"
         (Term.app `f [(Term.proj `i "." `succ)]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_⁻¹» (Term.app `f [`i]) "⁻¹") "*" (Term.app `f [(Term.proj `i "." `succ)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.proj `i "." `succ)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `i "." `succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_⁻¹» (Term.app `f [`i]) "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`i]) ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`i]
       []
       "=>"
       («term_*_»
        («term_⁻¹» (Term.paren "(" (Term.app `f [`i]) ")") "⁻¹")
        "*"
        (Term.app `f [(Term.proj `i "." `succ)]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app `single [(Term.app `f [(num "0")]) `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [(num "0")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 101, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj (Term.app `toTensor [`k `G `n]) "." `hom) [(Term.app `single [`f `m])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [`f `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `single [`f `m]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `toTensor [`k `G `n]) "." `hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `toTensor [`k `G `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `toTensor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `toTensor [`k `G `n]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ⁺¹._@.RepresentationTheory.GroupCohomologyResolution._hyg.43'
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
@[ simp ]
  theorem
    to_tensor_single
    ( f : Gⁿ⁺¹ ) ( m : k )
      : toTensor k G n . hom single f m = single f 0 m ⊗ₜ single fun i => f i ⁻¹ * f i . succ 1
    := to_tensor_aux_single _ _
#align group_cohomology.resolution.to_tensor_single GroupCohomology.Resolution.to_tensor_single

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
      (Command.declId `of_tensor_single [])
      (Command.declSig
       [(Term.explicitBinder "(" [`g] [":" `G] [] ")")
        (Term.explicitBinder "(" [`m] [":" `k] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":"
          (Data.Finsupp.Defs.«term_→₀_»
           (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
           " →₀ "
           `k)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app `ofTensor [`k `G `n]) "." `hom)
          [(TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
            (Term.app `single [`g `m])
            " ⊗ₜ "
            `x)])
         "="
         (Term.app
          `Finsupp.lift
          [(Term.app
            `RepCat.ofMulAction
            [`k `G (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")])
           `k
           (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
           (Term.fun
            "fun"
            (Term.basicFun
             [`f]
             []
             "=>"
             (Term.app
              `single
              [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])))
           `x]))))
      (Command.declValSimple
       ":="
       (Term.app `of_tensor_aux_single [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `of_tensor_aux_single [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of_tensor_aux_single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app `ofTensor [`k `G `n]) "." `hom)
        [(TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
          (Term.app `single [`g `m])
          " ⊗ₜ "
          `x)])
       "="
       (Term.app
        `Finsupp.lift
        [(Term.app
          `RepCat.ofMulAction
          [`k `G (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")])
         `k
         (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
         (Term.fun
          "fun"
          (Term.basicFun
           [`f]
           []
           "=>"
           (Term.app
            `single
            [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])))
         `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finsupp.lift
       [(Term.app
         `RepCat.ofMulAction
         [`k `G (RepresentationTheory.GroupCohomologyResolution.«termGⁿ⁺¹» "Gⁿ⁺¹")])
        `k
        (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
        (Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
          (Term.app
           `single
           [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])))
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
        [`f]
        []
        "=>"
        (Term.app
         `single
         [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [(Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `partialProd [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `partialProd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`f]
       []
       "=>"
       (Term.app
        `single
        [(Term.paren "(" (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `partialProd [`f])) ")")
         `m])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ._@.RepresentationTheory.GroupCohomologyResolution._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    of_tensor_single
    ( g : G ) ( m : k ) ( x : Gⁿ →₀ k )
      :
        ofTensor k G n . hom single g m ⊗ₜ x
          =
          Finsupp.lift RepCat.ofMulAction k G Gⁿ⁺¹ k Gⁿ fun f => single g • partialProd f m x
    := of_tensor_aux_single _ _ _
#align group_cohomology.resolution.of_tensor_single GroupCohomology.Resolution.of_tensor_single

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `of_tensor_single' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`g] [":" (Data.Finsupp.Defs.«term_→₀_» `G " →₀ " `k)] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")]
         []
         ")")
        (Term.explicitBinder "(" [`m] [":" `k] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app `ofTensor [`k `G `n]) "." `hom)
          [(TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
            `g
            " ⊗ₜ "
            (Term.app `single [`x `m]))])
         "="
         (Term.app
          `Finsupp.lift
          [(Term.hole "_")
           `k
           `G
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (Term.app
              `single
              [(Algebra.Group.Defs.«term_•_» `a " • " (Term.app `partialProd [`x])) `m])))
           `g]))))
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
            ["["
             [(Tactic.simpLemma [] [] `of_tensor) "," (Tactic.simpLemma [] [] `of_tensor_aux)]
             "]"]
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
           ["["
            [(Tactic.simpLemma [] [] `of_tensor) "," (Tactic.simpLemma [] [] `of_tensor_aux)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `of_tensor) "," (Tactic.simpLemma [] [] `of_tensor_aux)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_tensor_aux
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_tensor
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app `ofTensor [`k `G `n]) "." `hom)
        [(TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
          `g
          " ⊗ₜ "
          (Term.app `single [`x `m]))])
       "="
       (Term.app
        `Finsupp.lift
        [(Term.hole "_")
         `k
         `G
         (Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.app
            `single
            [(Algebra.Group.Defs.«term_•_» `a " • " (Term.app `partialProd [`x])) `m])))
         `g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Finsupp.lift
       [(Term.hole "_")
        `k
        `G
        (Term.fun
         "fun"
         (Term.basicFun
          [`a]
          []
          "=>"
          (Term.app
           `single
           [(Algebra.Group.Defs.«term_•_» `a " • " (Term.app `partialProd [`x])) `m])))
        `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.app
         `single
         [(Algebra.Group.Defs.«term_•_» `a " • " (Term.app `partialProd [`x])) `m])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [(Algebra.Group.Defs.«term_•_» `a " • " (Term.app `partialProd [`x])) `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `a " • " (Term.app `partialProd [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `partialProd [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `partialProd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `a " • " (Term.app `partialProd [`x]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`a]
       []
       "=>"
       (Term.app
        `single
        [(Term.paren "(" (Algebra.Group.Defs.«term_•_» `a " • " (Term.app `partialProd [`x])) ")")
         `m])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Finsupp.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj (Term.app `ofTensor [`k `G `n]) "." `hom)
       [(TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»
         `g
         " ⊗ₜ "
         (Term.app `single [`x `m]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_» `g " ⊗ₜ " (Term.app `single [`x `m]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `single [`x `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `single
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 100, (some 101,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (TensorProduct.LinearAlgebra.TensorProduct.«term_⊗ₜ_» `g " ⊗ₜ " (Term.app `single [`x `m]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `ofTensor [`k `G `n]) "." `hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ofTensor [`k `G `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ofTensor
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ofTensor [`k `G `n]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (RepresentationTheory.GroupCohomologyResolution.«termGⁿ» "Gⁿ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RepresentationTheory.GroupCohomologyResolution.«termGⁿ»', expected 'RepresentationTheory.GroupCohomologyResolution.termGⁿ._@.RepresentationTheory.GroupCohomologyResolution._hyg.6'
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
  of_tensor_single'
  ( g : G →₀ k ) ( x : Gⁿ ) ( m : k )
    :
      ofTensor k G n . hom g ⊗ₜ single x m
        =
        Finsupp.lift _ k G fun a => single a • partialProd x m g
  := by simp [ of_tensor , of_tensor_aux ]
#align group_cohomology.resolution.of_tensor_single' GroupCohomology.Resolution.of_tensor_single'

variable (k G n)

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. -/
def equivTensor :
    RepCat.ofMulAction k G (Fin (n + 1) → G) ≅
      RepCat.of
        ((Representation.ofMulAction k G G).tprod (1 : Representation k G ((Fin n → G) →₀ k))) :=
  ActionCat.mkIso
    (LinearEquiv.toModuleIso
      { toTensorAux k G n with
        invFun := ofTensorAux k G n
        left_inv := to_tensor_aux_left_inv
        right_inv := fun x => by convert to_tensor_aux_right_inv x })
    (toTensor k G n).comm
#align group_cohomology.resolution.equiv_tensor GroupCohomology.Resolution.equivTensor

@[simp]
theorem equiv_tensor_def : (equivTensor k G n).hom = toTensor k G n :=
  rfl
#align group_cohomology.resolution.equiv_tensor_def GroupCohomology.Resolution.equiv_tensor_def

@[simp]
theorem equiv_tensor_inv_def : (equivTensor k G n).inv = ofTensor k G n :=
  rfl
#align
  group_cohomology.resolution.equiv_tensor_inv_def GroupCohomology.Resolution.equiv_tensor_inv_def

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `tensor_product.left_module`, whilst that of the righthand side comes from
`representation.as_module`. Allows us to use `basis.algebra_tensor_product` to get a `k[G]`-basis
of the righthand side. -/
def ofMulActionBasisAux :
    MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k) ≃ₗ[MonoidAlgebra k G]
      (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  { (RepCat.equivalenceModuleMonoidAlgebra.1.mapIso (equivTensor k G n).symm).toLinearEquiv with
    map_smul' := fun r x =>
      by
      rw [RingHom.id_apply, LinearEquiv.to_fun_eq_coe, ← LinearEquiv.map_smul]
      congr 1
      refine' x.induction_on _ (fun x y => _) fun y z hy hz => _
      · simp only [smul_zero]
      · simp only [TensorProduct.smul_tmul']
        show (r * x) ⊗ₜ y = _
        rw [← of_mul_action_self_smul_eq_mul, smul_tprod_one_as_module]
      · rw [smul_add, hz, hy, smul_add] }
#align
  group_cohomology.resolution.of_mul_action_basis_aux GroupCohomology.Resolution.ofMulActionBasisAux

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  @Basis.map _ (MonoidAlgebra k G) (MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k)) _ _ _ _ _ _
    (@Algebra.TensorProduct.basis k _ (MonoidAlgebra k G) _ _ ((Fin n → G) →₀ k) _ _ (Fin n → G)
      ⟨LinearEquiv.refl k _⟩)
    (ofMulActionBasisAux k G n)
#align group_cohomology.resolution.of_mul_action_basis GroupCohomology.Resolution.ofMulActionBasis

theorem ofMulActionFree :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).AsModule :=
  Module.Free.ofBasis (ofMulActionBasis k G n)
#align group_cohomology.resolution.of_mul_action_free GroupCohomology.Resolution.ofMulActionFree

end Basis

end GroupCohomology.resolution

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
def classifyingSpaceUniversalCover [Monoid G] : SimplicialObject (ActionCat (Type u) <| MonCat.of G)
    where
  obj n := ActionCat.ofMulAction G (Fin (n.unop.len + 1) → G)
  map m n f :=
    { hom := fun x => x ∘ f.unop.toOrderHom
      comm' := fun g => rfl }
  map_id' n := rfl
  map_comp' i j k f g := rfl
#align classifying_space_universal_cover classifyingSpaceUniversalCover

namespace classifyingSpaceUniversalCover

open CategoryTheory CategoryTheory.Limits

variable [Monoid G]

/-- When the category is `G`-Set, `cech_nerve_terminal_from` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cechNerveTerminalFromIso :
    cechNerveTerminalFrom (ActionCat.ofMulAction G G) ≅ classifyingSpaceUniversalCover G :=
  (NatIso.ofComponents fun n => limit.isoLimitCone (ActionCat.ofMulActionLimitCone _ _))
    fun m n f =>
    by
    refine' is_limit.hom_ext (ActionCat.ofMulActionLimitCone.{u, 0} _ _).2 fun j => _
    dsimp only [cech_nerve_terminal_from, pi.lift]
    dsimp
    rw [category.assoc, limit.iso_limit_cone_hom_π, limit.lift_π, category.assoc]
    exact (limit.iso_limit_cone_hom_π _ _).symm
#align
  classifying_space_universal_cover.cech_nerve_terminal_from_iso classifyingSpaceUniversalCover.cechNerveTerminalFromIso

/-- As a simplicial set, `cech_nerve_terminal_from` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ :=
  (NatIso.ofComponents fun n => Types.productIso _) fun m n f =>
    Matrix.ext fun i j => Types.Limit.lift_π_apply _ _ _ _
#align
  classifying_space_universal_cover.cech_nerve_terminal_from_iso_comp_forget classifyingSpaceUniversalCover.cechNerveTerminalFromIsoCompForget

variable (k G)

open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`. -/
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  (SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
      (terminal.from _))
    fun i g h => Subsingleton.elim _ _
#align
  classifying_space_universal_cover.comp_forget_augmented classifyingSpaceUniversalCover.compForgetAugmented

/-- The augmented Čech nerve of the map from `fin 1 → G` to the terminal object in `Type u` has an
extra degeneracy. -/
def extraDegeneracyAugmentedCechNerve :
    ExtraDegeneracy (arrow.mk <| terminal.from G).augmentedCechNerve :=
  augmentedCechNerve.extraDegeneracy (arrow.mk <| terminal.from G)
    ⟨fun x => (1 : G),
      @Subsingleton.elim _ (@Unique.subsingleton _ (Limits.uniqueToTerminal _)) _ _⟩
#align
  classifying_space_universal_cover.extra_degeneracy_augmented_cech_nerve classifyingSpaceUniversalCover.extraDegeneracyAugmentedCechNerve

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) :=
  by
  refine'
    extra_degeneracy.of_iso (_ : (arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extra_degeneracy_augmented_cech_nerve G)
  exact
    comma.iso_mk (cech_nerve_terminal_from.iso G ≪≫ cech_nerve_terminal_from_iso_comp_forget G)
      (iso.refl _) (by ext : 2 <;> apply is_terminal.hom_ext terminal_is_terminal)
#align
  classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented

/-- The free functor `Type u ⥤ Module.{u} k` applied to the universal cover of the classifying
space of `G` as a simplicial set, augmented by the map from `fin 1 → G` to the terminal object
in `Type u`. -/
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free k)).obj (compForgetAugmented G)
#align
  classifying_space_universal_cover.comp_forget_augmented.to_Module classifyingSpaceUniversalCover.compForgetAugmented.toModule

/-- If we augment the universal cover of the classifying space of `G` as a simplicial set by the
map from `fin 1 → G` to the terminal object in `Type u`, then apply the free functor
`Type u ⥤ Module.{u} k`, the resulting augmented simplicial `k`-module has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmentedToModule :
    ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  ExtraDegeneracy.map (extraDegeneracyCompForgetAugmented G) (ModuleCat.free k)
#align
  classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented_to_Module classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmentedToModule

end classifyingSpaceUniversalCover

variable (k)

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def GroupCohomology.resolution [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (RepCat k G)).obj
    (classifyingSpaceUniversalCover G ⋙ (RepCat.linearization k G).1.1)
#align group_cohomology.resolution GroupCohomology.resolution

namespace GroupCohomology.resolution

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable (k G) [Monoid G]

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (G : Type u) (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (Fin n → G) →₀ k :=
  Finsupp.lift ((Fin n → G) →₀ k) k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).Sum fun p =>
      Finsupp.single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))
#align group_cohomology.resolution.d GroupCohomology.resolution.d

variable {k G}

@[simp]
theorem d_of {G : Type u} {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (Finsupp.single c 1) =
      Finset.univ.Sum fun p : Fin (n + 1) =>
        Finsupp.single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) :=
  by simp [d]
#align group_cohomology.resolution.d_of GroupCohomology.resolution.d_of

variable (k G)

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def xIso (n : ℕ) :
    (GroupCohomology.resolution k G).x n ≅ RepCat.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _
#align group_cohomology.resolution.X_iso GroupCohomology.resolution.xIso

theorem X_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((GroupCohomology.resolution k G).x n) :=
  RepCat.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of (MonoidAlgebra k G) (Representation.ofMulAction k G (Fin (n + 1) → G)).AsModule)
      _ (ofMulActionBasis k G n)
#align group_cohomology.resolution.X_projective GroupCohomology.resolution.X_projective

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) : ((GroupCohomology.resolution k G).d (n + 1) n).hom = d k G (n + 1) :=
  by
  ext (x y)
  dsimp [GroupCohomology.resolution]
  simpa [← @int_cast_smul k, simplicial_object.δ]
#align group_cohomology.resolution.d_eq GroupCohomology.resolution.d_eq

section Exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModule :=
  ((forget₂ (RepCat k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
    (GroupCohomology.resolution k G)
#align group_cohomology.resolution.forget₂_to_Module GroupCohomology.resolution.forget₂ToModule

/-- If we apply the free functor `Type u ⥤ Module.{u} k` to the universal cover of the classifying
space of `G` as a simplicial set, then take the alternating face map complex, the result is
isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      GroupCohomology.resolution.forget₂ToModule k G :=
  eqToIso
    (Functor.congr_obj
      (map_alternating_face_map_complex (forget₂ (RepCat k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ (RepCat.linearization k G).1.1))
#align
  group_cohomology.resolution.comp_forget_augmented_iso GroupCohomology.resolution.compForgetAugmentedIso

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂ToModuleHomotopyEquiv :
    HomotopyEquiv (GroupCohomology.resolution.forget₂ToModule k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj
        ((forget₂ (RepCat k G) _).obj <| RepCat.of Representation.trivial)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (@Finsupp.LinearEquiv.finsuppUnique k k _ _ _ (⊤_ Type u)
              Types.terminalIso.toEquiv.unique).toModuleIso)
#align
  group_cohomology.resolution.forget₂_to_Module_homotopy_equiv GroupCohomology.resolution.forget₂ToModuleHomotopyEquiv

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def ε : RepCat.ofMulAction k G (Fin 1 → G) ⟶ RepCat.of Representation.trivial
    where
  hom := Finsupp.total _ _ _ fun f => (1 : k)
  comm' g := by
    ext
    show
      Finsupp.total (Fin 1 → G) k k (fun f => (1 : k)) (Finsupp.mapDomain _ (Finsupp.single _ _)) =
        Finsupp.total _ _ _ _ (Finsupp.single _ _)
    simp only [Finsupp.map_domain_single, Finsupp.total_single]
#align group_cohomology.resolution.ε GroupCohomology.resolution.ε

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂_to_Module_homotopy_equiv_f_0_eq :
    (forget₂ToModuleHomotopyEquiv k G).1.f 0 = (forget₂ (RepCat k G) _).map (ε k G) :=
  by
  show (HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _).f 0 = _
  simp only [HomologicalComplex.comp_f]
  convert category.id_comp _
  · dsimp only [HomotopyEquiv.ofIso, comp_forget_augmented_iso, map_alternating_face_map_complex]
    simp only [iso.symm_hom, eq_to_iso.inv, HomologicalComplex.eq_to_hom_f, eq_to_hom_refl]
  trans (Finsupp.total _ _ _ fun f => (1 : k)).comp ((ModuleCat.free k).map (terminal.from _))
  · dsimp
    rw [@Finsupp.lmap_domain_total (Fin 1 → G) k k _ _ _ (⊤_ Type u) k _ _ (fun i => (1 : k))
        (fun i => (1 : k))
        (terminal.from
          ((classifyingSpaceUniversalCover G).obj (Opposite.op (SimplexCategory.mk 0))).V)
        LinearMap.id fun i => rfl,
      LinearMap.id_comp]
    rfl
  · congr
    · ext
      dsimp [HomotopyEquiv.ofIso]
      rw [Finsupp.total_single, one_smul, @Unique.eq_default _ types.terminal_iso.to_equiv.unique a,
        Finsupp.single_eq_same]
    · exact @Subsingleton.elim _ (@Unique.subsingleton _ (limits.unique_to_terminal _)) _ _
#align
  group_cohomology.resolution.forget₂_to_Module_homotopy_equiv_f_0_eq GroupCohomology.resolution.forget₂_to_Module_homotopy_equiv_f_0_eq

theorem d_comp_ε : (GroupCohomology.resolution k G).d 1 0 ≫ ε k G = 0 :=
  by
  ext1
  refine' LinearMap.ext fun x => _
  have : (forget₂_to_Module k G).d 1 0 ≫ (forget₂ (RepCat k G) (ModuleCat.{u} k)).map (ε k G) = 0 :=
    by
    rw [← forget₂_to_Module_homotopy_equiv_f_0_eq, ←
        (forget₂_to_Module_homotopy_equiv k G).1.2 1 0 rfl] <;>
      exact comp_zero
  exact LinearMap.ext_iff.1 this _
#align group_cohomology.resolution.d_comp_ε GroupCohomology.resolution.d_comp_ε

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
def εToSingle₀ :
    GroupCohomology.resolution k G ⟶
      (ChainComplex.single₀ _).obj (RepCat.of Representation.trivial) :=
  ((GroupCohomology.resolution k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩
#align group_cohomology.resolution.ε_to_single₀ GroupCohomology.resolution.εToSingle₀

theorem ε_to_single₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (ChainComplex.single₀MapHomologicalComplex _).hom.app _ =
      (forget₂ToModuleHomotopyEquiv k G).hom :=
  by
  refine' ChainComplex.to_single₀_ext _ _ _
  dsimp
  rw [category.comp_id]
  exact (forget₂_to_Module_homotopy_equiv_f_0_eq k G).symm
#align
  group_cohomology.resolution.ε_to_single₀_comp_eq GroupCohomology.resolution.ε_to_single₀_comp_eq

theorem quasiIsoOfForget₂εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) :=
  by
  have h : QuasiIso (forget₂_to_Module_homotopy_equiv k G).hom := HomotopyEquiv.toQuasiIso _
  rw [← ε_to_single₀_comp_eq k G] at h
  haveI := h
  exact quasiIsoOfCompRight _ ((ChainComplex.single₀MapHomologicalComplex _).hom.app _)
#align
  group_cohomology.resolution.quasi_iso_of_forget₂_ε_to_single₀ GroupCohomology.resolution.quasiIsoOfForget₂εToSingle₀

instance : QuasiIso (εToSingle₀ k G) :=
  (forget₂ _ (ModuleCat.{u} k)).quasiIsoOfMapQuasiIso _ (quasiIsoOfForget₂εToSingle₀ k G)

end Exactness

end GroupCohomology.resolution

open GroupCohomology.resolution

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def GroupCohomology.projectiveResolution :
    ProjectiveResolutionCat (RepCat.of (@Representation.trivial k G _ _)) :=
  (εToSingle₀ k G).toSingle₀ProjectiveResolution (X_projective k G)
#align group_cohomology.ProjectiveResolution GroupCohomology.projectiveResolution

instance : EnoughProjectives (RepCat k G) :=
  RepCat.equivalenceModuleMonoidAlgebra.enough_projectives_iff.2
    ModuleCat.Module_enough_projectives.{u}

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `group_cohomology.resolution k G`. -/
def GroupCohomology.extIso (V : RepCat k G) (n : ℕ) :
    ((ext k (RepCat k G) n).obj (Opposite.op <| RepCat.of Representation.trivial)).obj V ≅
      (((((linearYoneda k (RepCat k G)).obj V).rightOp.mapHomologicalComplex _).obj
              (GroupCohomology.resolution k G)).homology
          n).unop :=
  by
  let this :=
      (((linear_yoneda k (RepCat k G)).obj V).rightOp.leftDerivedObjIso n
            (GroupCohomology.projectiveResolution k G)).unop.symm <;>
    exact this
#align group_cohomology.Ext_iso GroupCohomology.extIso

