/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.l2_space
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.NormedSpace.LpSpace
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Hilbert sum of a family of inner product spaces

Given a family `(G : ι → Type*) [Π i, inner_product_space 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑' i, ‖f i‖ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the *Hilbert sum* of the family `G`.  By choosing
`G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this construction.

We also define a *predicate* `is_hilbert_sum 𝕜 E V`, where `V : Π i, G i →ₗᵢ[𝕜] E`, expressing that
`V` is an `orthogonal_family` and that the associated map `lp G 2 →ₗᵢ[𝕜] E` is surjective.

## Main definitions

* `orthogonal_family.linear_isometry`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with
  mutually-orthogonal images, there is an induced isometric embedding of the Hilbert sum of `G`
  into `E`.

* `is_hilbert_sum`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E`,
  `is_hilbert_sum 𝕜 E V` means that `V` is an `orthogonal_family` and that the above
  linear isometry is surjective.

* `is_hilbert_sum.linear_isometry_equiv`: If a Hilbert space `E` is a Hilbert sum of the
  inner product spaces `G i` with respect to the family `V : Π i, G i →ₗᵢ[𝕜] E`, then the
  corresponding `orthogonal_family.linear_isometry` can be upgraded to a `linear_isometry_equiv`.

* `hilbert_basis`: We define a *Hilbert basis* of a Hilbert space `E` to be a structure whose single
  field `hilbert_basis.repr` is an isometric isomorphism of `E` with `ℓ²(ι, 𝕜)` (i.e., the Hilbert
  sum of `ι` copies of `𝕜`).  This parallels the definition of `basis`, in `linear_algebra.basis`,
  as an isomorphism of an `R`-module with `ι →₀ R`.

* `hilbert_basis.has_coe_to_fun`: More conventionally a Hilbert basis is thought of as a family
  `ι → E` of vectors in `E` satisfying certain properties (orthonormality, completeness).  We obtain
  this interpretation of a Hilbert basis `b` by defining `⇑b`, of type `ι → E`, to be the image
  under `b.repr` of `lp.single 2 i (1:𝕜)`.  This parallels the definition `basis.has_coe_to_fun` in
  `linear_algebra.basis`.

* `hilbert_basis.mk`: Make a Hilbert basis of `E` from an orthonormal family `v : ι → E` of vectors
  in `E` whose span is dense.  This parallels the definition `basis.mk` in `linear_algebra.basis`.

* `hilbert_basis.mk_of_orthogonal_eq_bot`: Make a Hilbert basis of `E` from an orthonormal family
  `v : ι → E` of vectors in `E` whose span has trivial orthogonal complement.

## Main results

* `lp.inner_product_space`: Construction of the inner product space instance on the Hilbert sum
  `lp G 2`.  Note that from the file `analysis.normed_space.lp_space`, the space `lp G 2` already
  held a normed space instance (`lp.normed_space`), and if each `G i` is a Hilbert space (i.e.,
  complete), then `lp G 2` was already known to be complete (`lp.complete_space`).  So the work
  here is to define the inner product and show it is compatible.

* `orthogonal_family.range_linear_isometry`: Given a family `G` of inner product spaces and a family
  `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with mutually-orthogonal
  images, the image of the embedding `orthogonal_family.linear_isometry` of the Hilbert sum of `G`
  into `E` is the closure of the span of the images of the `G i`.

* `hilbert_basis.repr_apply_apply`: Given a Hilbert basis `b` of `E`, the entry `b.repr x i` of
  `x`'s representation in `ℓ²(ι, 𝕜)` is the inner product `⟪b i, x⟫`.

* `hilbert_basis.has_sum_repr`: Given a Hilbert basis `b` of `E`, a vector `x` in `E` can be
  expressed as the "infinite linear combination" `∑' i, b.repr x i • b i` of the basis vectors
  `b i`, with coefficients given by the entries `b.repr x i` of `x`'s representation in `ℓ²(ι, 𝕜)`.

* `exists_hilbert_basis`: A Hilbert space admits a Hilbert basis.

## Keywords

Hilbert space, Hilbert sum, l2, Hilbert basis, unitary equivalence, isometric isomorphism
-/


open IsROrC Submodule Filter

open BigOperators Nnreal Ennreal Classical ComplexConjugate TopologicalSpace

noncomputable section

variable {ι : Type _}

variable {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [InnerProductSpace 𝕜 E] [cplt : CompleteSpace E]

variable {G : ι → Type _} [∀ i, InnerProductSpace 𝕜 (G i)]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

-- mathport name: «exprℓ²( , )»
notation "ℓ²(" ι ", " 𝕜 ")" => lp (fun i : ι => 𝕜) 2

/-! ### Inner product space structure on `lp G 2` -/


namespace lp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `summable_inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f `g] [":" (Term.app `lp [`G (num "2")])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Summable
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`i])
             ", "
             (Term.app `g [`i])
             "⟫")))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `summable_of_norm_bounded
             [(Term.fun
               "fun"
               (Term.basicFun
                [`i]
                []
                "=>"
                («term_*_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`i]) "‖"))))
              (Term.app `lp.summable_mul [(Term.hole "_") `f `g])
              (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.«tactic_<;>_»
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Real.is_conjugate_exponent_iff)] "]")
               [])
              "<;>"
              (Mathlib.Tactic.normNum "norm_num" [] [] []))])
           []
           (Tactic.intro "intro" [`i])
           []
           (Tactic.exact
            "exact"
            (Term.app `norm_inner_le_norm [(Term.hole "_") (Term.hole "_")]))])))
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
            `summable_of_norm_bounded
            [(Term.fun
              "fun"
              (Term.basicFun
               [`i]
               []
               "=>"
               («term_*_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`i]) "‖"))))
             (Term.app `lp.summable_mul [(Term.hole "_") `f `g])
             (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.«tactic_<;>_»
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Real.is_conjugate_exponent_iff)] "]")
              [])
             "<;>"
             (Mathlib.Tactic.normNum "norm_num" [] [] []))])
          []
          (Tactic.intro "intro" [`i])
          []
          (Tactic.exact
           "exact"
           (Term.app `norm_inner_le_norm [(Term.hole "_") (Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `norm_inner_le_norm [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_inner_le_norm [(Term.hole "_") (Term.hole "_")])
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
      `norm_inner_le_norm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.«tactic_<;>_»
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Real.is_conjugate_exponent_iff)] "]")
          [])
         "<;>"
         (Mathlib.Tactic.normNum "norm_num" [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Real.is_conjugate_exponent_iff)] "]")
        [])
       "<;>"
       (Mathlib.Tactic.normNum "norm_num" [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Real.is_conjugate_exponent_iff)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.is_conjugate_exponent_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `summable_of_norm_bounded
        [(Term.fun
          "fun"
          (Term.basicFun
           [`i]
           []
           "=>"
           («term_*_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`i]) "‖"))))
         (Term.app `lp.summable_mul [(Term.hole "_") `f `g])
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `summable_of_norm_bounded
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          («term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`i]) "‖"))))
        (Term.app `lp.summable_mul [(Term.hole "_") `f `g])
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `lp.summable_mul [(Term.hole "_") `f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lp.summable_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `lp.summable_mul [(Term.hole "_") `f `g])
     ")")
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
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
         "*"
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`i]) "‖"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`i]) "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`i]) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `g [`i]) "‖"))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `summable_of_norm_bounded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`i])
           ", "
           (Term.app `g [`i])
           "⟫")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`i])
         ", "
         (Term.app `g [`i])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`i])
       ", "
       (Term.app `g [`i])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  summable_inner
  ( f g : lp G 2 ) : Summable fun i => ⟪ f i , g i ⟫
  :=
    by
      refine' summable_of_norm_bounded fun i => ‖ f i ‖ * ‖ g i ‖ lp.summable_mul _ f g _
        · rw [ Real.is_conjugate_exponent_iff ] <;> norm_num
        intro i
        exact norm_inner_le_norm _ _
#align lp.summable_inner lp.summable_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec ":" (Term.app `InnerProductSpace [`𝕜 (Term.app `lp [`G (num "2")])])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`lp.normedSpace] "with"]
        [(Term.structInstField
          (Term.structInstLVal `inner [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Topology.Algebra.InfiniteSum.«term∑'_,_»
             "∑'"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             ", "
             (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
              "⟪"
              (Term.app `f [`i])
              ", "
              (Term.app `g [`i])
              "⟫")))))
         []
         (Term.structInstField
          (Term.structInstLVal `norm_sq_eq_inner [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(calcTactic
                 "calc"
                 (calcStep
                  («term_=_»
                   («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖") "^" (num "2"))
                   "="
                   («term_^_»
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖")
                    "^"
                    (Term.proj
                     (Term.typeAscription
                      "("
                      (num "2")
                      ":"
                      [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                      ")")
                     "."
                     `toReal)))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])]))))
                 [(calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     («term_^_»
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
                      "^"
                      (Term.proj
                       (Term.typeAscription
                        "("
                        (num "2")
                        ":"
                        [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                        ")")
                       "."
                       `toReal))))
                   ":="
                   (Term.app `lp.norm_rpow_eq_tsum [(Term.hole "_") `f]))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     («term_^_»
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
                      "^"
                      (num "2"))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Term.app
                      `re
                      [(Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                        "⟪"
                        (Term.app `f [`i])
                        ", "
                        (Term.app `f [`i])
                        "⟫")])))
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
                        ["[" [(Tactic.simpLemma [] [] `norm_sq_eq_inner)] "]"]
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Term.app
                     `re
                     [(Topology.Algebra.InfiniteSum.«term∑'_,_»
                       "∑'"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                       ", "
                       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                        "⟪"
                        (Term.app `f [`i])
                        ", "
                        (Term.app `f [`i])
                        "⟫"))]))
                   ":="
                   (Term.proj (Term.app `is_R_or_C.re_clm.map_tsum [(Term.hole "_")]) "." `symm))
                  (calcStep
                   («term_=_» (Term.hole "_") "=" (Term.hole "_"))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Mathlib.Tactic.normNum "norm_num" [] [] [])])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact "exact" (Term.app `summable_inner [`f `f]))])]))))))
         []
         (Term.structInstField
          (Term.structInstLVal `conj_sym [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(calcTactic
                 "calc"
                 (calcStep
                  («term_=_»
                   (Term.app
                    (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
                    [(Term.hole "_")])
                   "="
                   (Term.app
                    (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
                    [(Topology.Algebra.InfiniteSum.«term∑'_,_»
                      "∑'"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      ", "
                      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `g [`i])
                       ", "
                       (Term.app `f [`i])
                       "⟫"))]))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))
                 [(calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Term.app
                      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
                      [(Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                        "⟪"
                        (Term.app `g [`i])
                        ", "
                        (Term.app `f [`i])
                        "⟫")])))
                   ":="
                   `is_R_or_C.conj_cle.map_tsum)
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                      "⟪"
                      (Term.app `f [`i])
                      ", "
                      (Term.app `g [`i])
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
                        ["only"]
                        ["[" [(Tactic.simpLemma [] [] `inner_conj_sym)] "]"]
                        [])]))))
                  (calcStep
                   («term_=_» (Term.hole "_") "=" (Term.hole "_"))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])]))))))
         []
         (Term.structInstField
          (Term.structInstLVal `add_left [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f₁ `f₂ `g]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(calcTactic
                 "calc"
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                     "⟪"
                     (Term.app («term_+_» `f₁ "+" `f₂) [`i])
                     ", "
                     (Term.app `g [`i])
                     "⟫")))
                  ":="
                  (Term.hole "_"))
                 [(calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     («term_+_»
                      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `f₁ [`i])
                       ", "
                       (Term.app `g [`i])
                       "⟫")
                      "+"
                      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `f₂ [`i])
                       ", "
                       (Term.app `g [`i])
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
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `inner_add_left)
                          ","
                          (Tactic.simpLemma [] [] `Pi.add_apply)
                          ","
                          (Tactic.simpLemma [] [] `coe_fn_add)]
                         "]"]
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    («term_+_»
                     (Topology.Algebra.InfiniteSum.«term∑'_,_»
                      "∑'"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      ", "
                      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `f₁ [`i])
                       ", "
                       (Term.app `g [`i])
                       "⟫"))
                     "+"
                     (Topology.Algebra.InfiniteSum.«term∑'_,_»
                      "∑'"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      ", "
                      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `f₂ [`i])
                       ", "
                       (Term.app `g [`i])
                       "⟫"))))
                   ":="
                   (Term.app `tsum_add [(Term.hole "_") (Term.hole "_")]))
                  (calcStep
                   («term_=_» (Term.hole "_") "=" (Term.hole "_"))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
                []
                (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.congr "congr" [])])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact "exact" (Term.app `summable_inner [`f₁ `g]))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact "exact" (Term.app `summable_inner [`f₂ `g]))])]))))))
         []
         (Term.structInstField
          (Term.structInstLVal `smul_left [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g `c]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(calcTactic
                 "calc"
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                     "⟪"
                     (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                     ", "
                     (Term.app `g [`i])
                     "⟫")))
                  ":="
                  (Term.hole "_"))
                 [(calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     («term_*_»
                      (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
                      "*"
                      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `f [`i])
                       ", "
                       (Term.app `g [`i])
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
                        ["only"]
                        ["[" [(Tactic.simpLemma [] [] `inner_smul_left)] "]"]
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    («term_*_»
                     (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
                     "*"
                     (Topology.Algebra.InfiniteSum.«term∑'_,_»
                      "∑'"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      ", "
                      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `f [`i])
                       ", "
                       (Term.app `g [`i])
                       "⟫"))))
                   ":="
                   `tsum_mul_left)
                  (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" (Term.hole "_"))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `coe_fn_smul)
                     ","
                     (Tactic.simpLemma [] [] `Pi.smul_apply)]
                    "]"]
                   [])])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.congr "congr" [])])]))))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`lp.normedSpace] "with"]
       [(Term.structInstField
         (Term.structInstLVal `inner [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Topology.Algebra.InfiniteSum.«term∑'_,_»
            "∑'"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            ", "
            (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`i])
             ", "
             (Term.app `g [`i])
             "⟫")))))
        []
        (Term.structInstField
         (Term.structInstLVal `norm_sq_eq_inner [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(calcTactic
                "calc"
                (calcStep
                 («term_=_»
                  («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖") "^" (num "2"))
                  "="
                  («term_^_»
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖")
                   "^"
                   (Term.proj
                    (Term.typeAscription
                     "("
                     (num "2")
                     ":"
                     [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                     ")")
                    "."
                    `toReal)))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])]))))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    («term_^_»
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
                     "^"
                     (Term.proj
                      (Term.typeAscription
                       "("
                       (num "2")
                       ":"
                       [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                       ")")
                      "."
                      `toReal))))
                  ":="
                  (Term.app `lp.norm_rpow_eq_tsum [(Term.hole "_") `f]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    («term_^_»
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `f [`i]) "‖")
                     "^"
                     (num "2"))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    (Term.app
                     `re
                     [(Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `f [`i])
                       ", "
                       (Term.app `f [`i])
                       "⟫")])))
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
                       ["[" [(Tactic.simpLemma [] [] `norm_sq_eq_inner)] "]"]
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Term.app
                    `re
                    [(Topology.Algebra.InfiniteSum.«term∑'_,_»
                      "∑'"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      ", "
                      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `f [`i])
                       ", "
                       (Term.app `f [`i])
                       "⟫"))]))
                  ":="
                  (Term.proj (Term.app `is_R_or_C.re_clm.map_tsum [(Term.hole "_")]) "." `symm))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (Term.hole "_"))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Mathlib.Tactic.normNum "norm_num" [] [] [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact "exact" (Term.app `summable_inner [`f `f]))])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `conj_sym [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(calcTactic
                "calc"
                (calcStep
                 («term_=_»
                  (Term.app
                   (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
                   [(Term.hole "_")])
                  "="
                  (Term.app
                   (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
                   [(Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                      "⟪"
                      (Term.app `g [`i])
                      ", "
                      (Term.app `f [`i])
                      "⟫"))]))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    (Term.app
                     (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
                     [(Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                       "⟪"
                       (Term.app `g [`i])
                       ", "
                       (Term.app `f [`i])
                       "⟫")])))
                  ":="
                  `is_R_or_C.conj_cle.map_tsum)
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                     "⟪"
                     (Term.app `f [`i])
                     ", "
                     (Term.app `g [`i])
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
                       ["only"]
                       ["[" [(Tactic.simpLemma [] [] `inner_conj_sym)] "]"]
                       [])]))))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (Term.hole "_"))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `add_left [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f₁ `f₂ `g]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(calcTactic
                "calc"
                (calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  (Topology.Algebra.InfiniteSum.«term∑'_,_»
                   "∑'"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                   ", "
                   (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                    "⟪"
                    (Term.app («term_+_» `f₁ "+" `f₂) [`i])
                    ", "
                    (Term.app `g [`i])
                    "⟫")))
                 ":="
                 (Term.hole "_"))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    («term_+_»
                     (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                      "⟪"
                      (Term.app `f₁ [`i])
                      ", "
                      (Term.app `g [`i])
                      "⟫")
                     "+"
                     (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                      "⟪"
                      (Term.app `f₂ [`i])
                      ", "
                      (Term.app `g [`i])
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
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `inner_add_left)
                         ","
                         (Tactic.simpLemma [] [] `Pi.add_apply)
                         ","
                         (Tactic.simpLemma [] [] `coe_fn_add)]
                        "]"]
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_+_»
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                      "⟪"
                      (Term.app `f₁ [`i])
                      ", "
                      (Term.app `g [`i])
                      "⟫"))
                    "+"
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                      "⟪"
                      (Term.app `f₂ [`i])
                      ", "
                      (Term.app `g [`i])
                      "⟫"))))
                  ":="
                  (Term.app `tsum_add [(Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (Term.hole "_"))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.congr "congr" [])]))))])
               []
               (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.congr "congr" [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact "exact" (Term.app `summable_inner [`f₁ `g]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.exact "exact" (Term.app `summable_inner [`f₂ `g]))])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `smul_left [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g `c]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(calcTactic
                "calc"
                (calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  (Topology.Algebra.InfiniteSum.«term∑'_,_»
                   "∑'"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                   ", "
                   (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                    "⟪"
                    (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                    ", "
                    (Term.app `g [`i])
                    "⟫")))
                 ":="
                 (Term.hole "_"))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Topology.Algebra.InfiniteSum.«term∑'_,_»
                    "∑'"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    («term_*_»
                     (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
                     "*"
                     (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                      "⟪"
                      (Term.app `f [`i])
                      ", "
                      (Term.app `g [`i])
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
                       ["only"]
                       ["[" [(Tactic.simpLemma [] [] `inner_smul_left)] "]"]
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_*_»
                    (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
                    "*"
                    (Topology.Algebra.InfiniteSum.«term∑'_,_»
                     "∑'"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                     ", "
                     (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                      "⟪"
                      (Term.app `f [`i])
                      ", "
                      (Term.app `g [`i])
                      "⟫"))))
                  ":="
                  `tsum_mul_left)
                 (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" (Term.hole "_"))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `coe_fn_smul)
                    ","
                    (Tactic.simpLemma [] [] `Pi.smul_apply)]
                   "]"]
                  [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.congr "congr" [])])]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `c]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(calcTactic
             "calc"
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Topology.Algebra.InfiniteSum.«term∑'_,_»
                "∑'"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                ", "
                (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                 "⟪"
                 (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
                 ", "
                 (Term.app `g [`i])
                 "⟫")))
              ":="
              (Term.hole "_"))
             [(calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Topology.Algebra.InfiniteSum.«term∑'_,_»
                 "∑'"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                 ", "
                 («term_*_»
                  (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
                  "*"
                  (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                   "⟪"
                   (Term.app `f [`i])
                   ", "
                   (Term.app `g [`i])
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
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `inner_smul_left)] "]"]
                    [])]))))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_*_»
                 (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
                 "*"
                 (Topology.Algebra.InfiniteSum.«term∑'_,_»
                  "∑'"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                  ", "
                  (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                   "⟪"
                   (Term.app `f [`i])
                   ", "
                   (Term.app `g [`i])
                   "⟫"))))
               ":="
               `tsum_mul_left)
              (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" (Term.hole "_"))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `coe_fn_smul) "," (Tactic.simpLemma [] [] `Pi.smul_apply)]
                "]"]
               [])])
            []
            (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.congr "congr" [])])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(calcTactic
           "calc"
           (calcStep
            («term_=_»
             (Term.hole "_")
             "="
             (Topology.Algebra.InfiniteSum.«term∑'_,_»
              "∑'"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
               "⟪"
               (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
               ", "
               (Term.app `g [`i])
               "⟫")))
            ":="
            (Term.hole "_"))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (Topology.Algebra.InfiniteSum.«term∑'_,_»
               "∑'"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               («term_*_»
                (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
                "*"
                (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                 "⟪"
                 (Term.app `f [`i])
                 ", "
                 (Term.app `g [`i])
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
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `inner_smul_left)] "]"]
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
               "*"
               (Topology.Algebra.InfiniteSum.«term∑'_,_»
                "∑'"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                ", "
                (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
                 "⟪"
                 (Term.app `f [`i])
                 ", "
                 (Term.app `g [`i])
                 "⟫"))))
             ":="
             `tsum_mul_left)
            (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" (Term.hole "_"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `coe_fn_smul) "," (Tactic.simpLemma [] [] `Pi.smul_apply)]
              "]"]
             [])])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.congr "congr" [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.congr "congr" [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `coe_fn_smul) "," (Tactic.simpLemma [] [] `Pi.smul_apply)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `coe_fn_smul) "," (Tactic.simpLemma [] [] `Pi.smul_apply)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_fn_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Topology.Algebra.InfiniteSum.«term∑'_,_»
          "∑'"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
           "⟪"
           (Algebra.Group.Defs.«term_•_» `c " • " (Term.app `f [`i]))
           ", "
           (Term.app `g [`i])
           "⟫")))
        ":="
        (Term.hole "_"))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Topology.Algebra.InfiniteSum.«term∑'_,_»
           "∑'"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
           ", "
           («term_*_»
            (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
            "*"
            (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`i])
             ", "
             (Term.app `g [`i])
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
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `inner_smul_left)] "]"]
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
           "*"
           (Topology.Algebra.InfiniteSum.«term∑'_,_»
            "∑'"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            ", "
            (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`i])
             ", "
             (Term.app `g [`i])
             "⟫"))))
         ":="
         `tsum_mul_left)
        (calcStep («term_=_» (Term.hole "_") "=" (Term.hole "_")) ":=" (Term.hole "_"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      `tsum_mul_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
        "*"
        (Topology.Algebra.InfiniteSum.«term∑'_,_»
         "∑'"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.app `f [`i])
          ", "
          (Term.app `g [`i])
          "⟫"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") [`c])
       "*"
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`i])
         ", "
         (Term.app `g [`i])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app `f [`i])
        ", "
        (Term.app `g [`i])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`i])
       ", "
       (Term.app `g [`i])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : InnerProductSpace 𝕜 lp G 2
  :=
    {
      lp.normedSpace with
      inner := fun f g => ∑' i , ⟪ f i , g i ⟫
        norm_sq_eq_inner
          :=
          fun
            f
              =>
              by
                calc
                    ‖ f ‖ ^ 2 = ‖ f ‖ ^ ( 2 : ℝ≥0∞ ) . toReal := by norm_cast
                    _ = ∑' i , ‖ f i ‖ ^ ( 2 : ℝ≥0∞ ) . toReal := lp.norm_rpow_eq_tsum _ f
                      _ = ∑' i , ‖ f i ‖ ^ 2 := by norm_cast
                      _ = ∑' i , re ⟪ f i , f i ⟫ := by simp only [ norm_sq_eq_inner ]
                      _ = re ∑' i , ⟪ f i , f i ⟫ := is_R_or_C.re_clm.map_tsum _ . symm
                      _ = _ := by congr
                  · norm_num
                  · exact summable_inner f f
        conj_sym
          :=
          fun
            f g
              =>
              by
                calc
                  conj _ = conj ∑' i , ⟪ g i , f i ⟫ := by congr
                  _ = ∑' i , conj ⟪ g i , f i ⟫ := is_R_or_C.conj_cle.map_tsum
                    _ = ∑' i , ⟪ f i , g i ⟫ := by simp only [ inner_conj_sym ]
                    _ = _ := by congr
        add_left
          :=
          fun
            f₁ f₂ g
              =>
              by
                calc
                    _ = ∑' i , ⟪ f₁ + f₂ i , g i ⟫ := _
                    _ = ∑' i , ⟪ f₁ i , g i ⟫ + ⟪ f₂ i , g i ⟫
                        :=
                        by simp only [ inner_add_left , Pi.add_apply , coe_fn_add ]
                      _ = ∑' i , ⟪ f₁ i , g i ⟫ + ∑' i , ⟪ f₂ i , g i ⟫ := tsum_add _ _
                      _ = _ := by congr
                  · congr
                  · exact summable_inner f₁ g
                  · exact summable_inner f₂ g
        smul_left
          :=
          fun
            f g c
              =>
              by
                calc
                    _ = ∑' i , ⟪ c • f i , g i ⟫ := _
                    _ = ∑' i , conj c * ⟪ f i , g i ⟫ := by simp only [ inner_smul_left ]
                      _ = conj c * ∑' i , ⟪ f i , g i ⟫ := tsum_mul_left
                      _ = _ := _
                  · simp only [ coe_fn_smul , Pi.smul_apply ]
                  · congr
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_eq_tsum [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f `g] [":" (Term.app `lp [`G (num "2")])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `f ", " `g "⟫")
         "="
         (Topology.Algebra.InfiniteSum.«term∑'_,_»
          "∑'"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`i])
           ", "
           (Term.app `g [`i])
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
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `f ", " `g "⟫")
       "="
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`i])
         ", "
         (Term.app `g [`i])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.app `f [`i])
        ", "
        (Term.app `g [`i])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`i])
       ", "
       (Term.app `g [`i])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem inner_eq_tsum ( f g : lp G 2 ) : ⟪ f , g ⟫ = ∑' i , ⟪ f i , g i ⟫ := rfl
#align lp.inner_eq_tsum lp.inner_eq_tsum

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `has_sum_inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f `g] [":" (Term.app `lp [`G (num "2")])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasSum
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`i])
             ", "
             (Term.app `g [`i])
             "⟫")))
          (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `f ", " `g "⟫")])))
      (Command.declValSimple ":=" (Term.proj (Term.app `summable_inner [`f `g]) "." `HasSum) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `summable_inner [`f `g]) "." `HasSum)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `summable_inner [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `summable_inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `summable_inner [`f `g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasSum
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`i])
           ", "
           (Term.app `g [`i])
           "⟫")))
        (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `f ", " `g "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `f ", " `g "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  has_sum_inner
  ( f g : lp G 2 ) : HasSum fun i => ⟪ f i , g i ⟫ ⟪ f , g ⟫
  := summable_inner f g . HasSum
#align lp.has_sum_inner lp.has_sum_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_single_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" `ι] [] ")")
        (Term.explicitBinder "(" [`a] [":" (Term.app `G [`i])] [] ")")
        (Term.explicitBinder "(" [`f] [":" (Term.app `lp [`G (num "2")])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.app `lp.single [(num "2") `i `a])
          ", "
          `f
          "⟫")
         "="
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `a ", " (Term.app `f [`i]) "⟫"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj
              (Term.app `has_sum_inner [(Term.app `lp.single [(num "2") `i `a]) `f])
              "."
              `unique)
             [(Term.hole "_")]))
           []
           (convert
            "convert"
            []
            (Term.app
             `has_sum_ite_eq
             [`i
              (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `a ", " (Term.app `f [`i]) "⟫")])
            [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `lp.single_apply)] "]")
            [])
           []
           (Mathlib.Tactic.splitIfs "split_ifs" [] [])
           []
           (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.subst "subst" [`h])])
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.app `has_sum_inner [(Term.app `lp.single [(num "2") `i `a]) `f])
             "."
             `unique)
            [(Term.hole "_")]))
          []
          (convert
           "convert"
           []
           (Term.app
            `has_sum_ite_eq
            [`i
             (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `a ", " (Term.app `f [`i]) "⟫")])
           [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
           [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `lp.single_apply)] "]") [])
          []
          (Mathlib.Tactic.splitIfs "split_ifs" [] [])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.subst "subst" [`h])])
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
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.subst "subst" [`h])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `lp.single_apply)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lp.single_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `has_sum_ite_eq
        [`i (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `a ", " (Term.app `f [`i]) "⟫")])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `has_sum_ite_eq
       [`i (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `a ", " (Term.app `f [`i]) "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `a ", " (Term.app `f [`i]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
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
  inner_single_left
  ( i : ι ) ( a : G i ) ( f : lp G 2 ) : ⟪ lp.single 2 i a , f ⟫ = ⟪ a , f i ⟫
  :=
    by
      refine' has_sum_inner lp.single 2 i a f . unique _
        convert has_sum_ite_eq i ⟪ a , f i ⟫
        ext j
        rw [ lp.single_apply ]
        split_ifs
        · subst h
        · simp
#align lp.inner_single_left lp.inner_single_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_single_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" `ι] [] ")")
        (Term.explicitBinder "(" [`a] [":" (Term.app `G [`i])] [] ")")
        (Term.explicitBinder "(" [`f] [":" (Term.app `lp [`G (num "2")])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
          "⟪"
          `f
          ", "
          (Term.app `lp.single [(num "2") `i `a])
          "⟫")
         "="
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `f [`i]) ", " `a "⟫"))))
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
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inner_conj_sym)] "]")]
             ["using"
              (Term.app
               `congr_arg
               [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
                (Term.app `inner_single_left [`i `a `f])])]))])))
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
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inner_conj_sym)] "]")]
            ["using"
             (Term.app
              `congr_arg
              [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
               (Term.app `inner_single_left [`i `a `f])])]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inner_conj_sym)] "]")]
        ["using"
         (Term.app
          `congr_arg
          [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
           (Term.app `inner_single_left [`i `a `f])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
        (Term.app `inner_single_left [`i `a `f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inner_single_left [`i `a `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner_single_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `inner_single_left [`i `a `f])
     ")")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_conj_sym
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
        "⟪"
        `f
        ", "
        (Term.app `lp.single [(num "2") `i `a])
        "⟫")
       "="
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `f [`i]) ", " `a "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `f [`i]) ", " `a "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  inner_single_right
  ( i : ι ) ( a : G i ) ( f : lp G 2 ) : ⟪ f , lp.single 2 i a ⟫ = ⟪ f i , a ⟫
  := by simpa [ inner_conj_sym ] using congr_arg conj inner_single_left i a f
#align lp.inner_single_right lp.inner_single_right

end lp

/-! ### Identification of a general Hilbert space `E` with a Hilbert sum -/


namespace OrthogonalFamily

variable {V : ∀ i, G i →ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 V)

include cplt hV

protected theorem summable_of_lp (f : lp G 2) : Summable fun i => V i (f i) :=
  by
  rw [hV.summable_iff_norm_sq_summable]
  convert (lp.mem_ℓp f).Summable _
  · norm_cast
  · norm_num
#align orthogonal_family.summable_of_lp OrthogonalFamily.summable_of_lp

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
protected def linearIsometry : lp G 2 →ₗᵢ[𝕜] E
    where
  toFun f := ∑' i, V i (f i)
  map_add' f g := by
    simp only [tsum_add (hV.summable_of_lp f) (hV.summable_of_lp g), lp.coe_fn_add, Pi.add_apply,
      LinearIsometry.map_add]
  map_smul' c f := by
    simpa only [LinearIsometry.map_smul, Pi.smul_apply, lp.coe_fn_smul] using
      tsum_const_smul (hV.summable_of_lp f)
  norm_map' f := by
    classical
      -- needed for lattice instance on `finset ι`, for `filter.at_top_ne_bot`
      have H : 0 < (2 : ℝ≥0∞).toReal := by norm_num
      suffices ‖∑' i : ι, V i (f i)‖ ^ (2 : ℝ≥0∞).toReal = ‖f‖ ^ (2 : ℝ≥0∞).toReal by
        exact Real.rpow_left_inj_on H.ne' (norm_nonneg _) (norm_nonneg _) this
      refine' tendsto_nhds_unique _ (lp.has_sum_norm H f)
      convert (hV.summable_of_lp f).HasSum.norm.rpow_const (Or.inr H.le)
      ext s
      exact_mod_cast (hV.norm_sum f s).symm
#align orthogonal_family.linear_isometry OrthogonalFamily.linearIsometry

protected theorem linear_isometry_apply (f : lp G 2) : hV.LinearIsometry f = ∑' i, V i (f i) :=
  rfl
#align orthogonal_family.linear_isometry_apply OrthogonalFamily.linear_isometry_apply

protected theorem has_sum_linear_isometry (f : lp G 2) :
    HasSum (fun i => V i (f i)) (hV.LinearIsometry f) :=
  (hV.summable_of_lp f).HasSum
#align orthogonal_family.has_sum_linear_isometry OrthogonalFamily.has_sum_linear_isometry

@[simp]
protected theorem linear_isometry_apply_single {i : ι} (x : G i) :
    hV.LinearIsometry (lp.single 2 i x) = V i x :=
  by
  rw [hV.linear_isometry_apply, ← tsum_ite_eq i (V i x)]
  congr
  ext j
  rw [lp.single_apply]
  split_ifs
  · subst h
  · simp
#align orthogonal_family.linear_isometry_apply_single OrthogonalFamily.linear_isometry_apply_single

@[simp]
protected theorem linear_isometry_apply_dfinsupp_sum_single (W₀ : Π₀ i : ι, G i) :
    hV.LinearIsometry (W₀.Sum (lp.single 2)) = W₀.Sum fun i => V i :=
  by
  have :
    hV.linear_isometry (∑ i in W₀.support, lp.single 2 i (W₀ i)) =
      ∑ i in W₀.support, hV.linear_isometry (lp.single 2 i (W₀ i)) :=
    hV.linear_isometry.to_linear_map.map_sum
  simp (config := { contextual := true }) [Dfinsupp.sum, this]
#align
  orthogonal_family.linear_isometry_apply_dfinsupp_sum_single OrthogonalFamily.linear_isometry_apply_dfinsupp_sum_single

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
protected theorem range_linear_isometry [∀ i, CompleteSpace (G i)] :
    hV.LinearIsometry.toLinearMap.range = (⨆ i, (V i).toLinearMap.range).topologicalClosure :=
  by
  refine' le_antisymm _ _
  · rintro x ⟨f, rfl⟩
    refine' mem_closure_of_tendsto (hV.has_sum_linear_isometry f) (eventually_of_forall _)
    intro s
    rw [SetLike.mem_coe]
    refine' sum_mem _
    intro i hi
    refine' mem_supr_of_mem i _
    exact LinearMap.mem_range_self _ (f i)
  · apply topological_closure_minimal
    · refine' supᵢ_le _
      rintro i x ⟨x, rfl⟩
      use lp.single 2 i x
      exact hV.linear_isometry_apply_single x
    exact hV.linear_isometry.isometry.uniform_inducing.is_complete_range.is_closed
#align orthogonal_family.range_linear_isometry OrthogonalFamily.range_linear_isometry

end OrthogonalFamily

section IsHilbertSum

variable (𝕜 E) (V : ∀ i, G i →ₗᵢ[𝕜] E) (F : ι → Submodule 𝕜 E)

include cplt

/-- Given a family of Hilbert spaces `G : ι → Type*`, a Hilbert sum of `G` consists of a Hilbert
space `E` and an orthogonal family `V : Π i, G i →ₗᵢ[𝕜] E` such that the induced isometry
`Φ : lp G 2 → E` is surjective.

Keeping in mind that `lp G 2` is "the" external Hilbert sum of `G : ι → Type*`, this is analogous
to `direct_sum.is_internal`, except that we don't express it in terms of actual submodules. -/
@[protect_proj]
structure IsHilbertSum : Prop where ofSurjective ::
  OrthogonalFamily : OrthogonalFamily 𝕜 V
  surjective_isometry : Function.Surjective OrthogonalFamily.LinearIsometry
#align is_hilbert_sum IsHilbertSum

variable {𝕜 E V}

/-- If `V : Π i, G i →ₗᵢ[𝕜] E` is an orthogonal family such that the supremum of the ranges of
`V i` is dense, then `(E, V)` is a Hilbert sum of `G`. -/
theorem IsHilbertSum.mk [∀ i, CompleteSpace <| G i] (hVortho : OrthogonalFamily 𝕜 V)
    (hVtotal : ⊤ ≤ (⨆ i, (V i).toLinearMap.range).topologicalClosure) : IsHilbertSum 𝕜 E V :=
  { OrthogonalFamily := hVortho
    surjective_isometry := by
      rw [← LinearIsometry.coe_to_linear_map]
      exact
        linear_map.range_eq_top.mp
          (eq_top_iff.mpr <| hVtotal.trans_eq hVortho.range_linear_isometry.symm) }
#align is_hilbert_sum.mk IsHilbertSum.mk

/-- This is `orthogonal_family.is_hilbert_sum` in the case of actual inclusions from subspaces. -/
theorem IsHilbertSum.mkInternal [∀ i, CompleteSpace <| F i]
    (hFortho : @OrthogonalFamily 𝕜 E _ _ _ (fun i => F i) _ fun i => (F i).subtypeₗᵢ)
    (hFtotal : ⊤ ≤ (⨆ i, F i).topologicalClosure) :
    @IsHilbertSum _ 𝕜 _ E _ _ (fun i => F i) _ fun i => (F i).subtypeₗᵢ :=
  IsHilbertSum.mk hFortho (by simpa [subtypeₗᵢ_to_linear_map, range_subtype] using hFtotal)
#align is_hilbert_sum.mk_internal IsHilbertSum.mkInternal

/-- *A* Hilbert sum `(E, V)` of `G` is canonically isomorphic to *the* Hilbert sum of `G`,
i.e `lp G 2`.

Note that this goes in the opposite direction from `orthogonal_family.linear_isometry`. -/
noncomputable def IsHilbertSum.linearIsometryEquiv (hV : IsHilbertSum 𝕜 E V) : E ≃ₗᵢ[𝕜] lp G 2 :=
  LinearIsometryEquiv.symm <|
    LinearIsometryEquiv.ofSurjective hV.OrthogonalFamily.LinearIsometry hV.surjective_isometry
#align is_hilbert_sum.linear_isometry_equiv IsHilbertSum.linearIsometryEquiv

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`. -/
protected theorem IsHilbertSum.linear_isometry_equiv_symm_apply (hV : IsHilbertSum 𝕜 E V)
    (w : lp G 2) : hV.LinearIsometryEquiv.symm w = ∑' i, V i (w i) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linear_isometry_apply]
#align is_hilbert_sum.linear_isometry_equiv_symm_apply IsHilbertSum.linear_isometry_equiv_symm_apply

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`, and this
sum indeed converges. -/
protected theorem IsHilbertSum.has_sum_linear_isometry_equiv_symm (hV : IsHilbertSum 𝕜 E V)
    (w : lp G 2) : HasSum (fun i => V i (w i)) (hV.LinearIsometryEquiv.symm w) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.has_sum_linear_isometry]
#align
  is_hilbert_sum.has_sum_linear_isometry_equiv_symm IsHilbertSum.has_sum_linear_isometry_equiv_symm

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, an "elementary basis vector" in `lp G 2` supported at `i : ι` is the image of the
associated element in `E`. -/
@[simp]
protected theorem IsHilbertSum.linear_isometry_equiv_symm_apply_single (hV : IsHilbertSum 𝕜 E V)
    {i : ι} (x : G i) : hV.LinearIsometryEquiv.symm (lp.single 2 i x) = V i x := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linear_isometry_apply_single]
#align
  is_hilbert_sum.linear_isometry_equiv_symm_apply_single IsHilbertSum.linear_isometry_equiv_symm_apply_single

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp]
protected theorem IsHilbertSum.linear_isometry_equiv_symm_apply_dfinsupp_sum_single
    (hV : IsHilbertSum 𝕜 E V) (W₀ : Π₀ i : ι, G i) :
    hV.LinearIsometryEquiv.symm (W₀.Sum (lp.single 2)) = W₀.Sum fun i => V i := by
  simp [IsHilbertSum.linearIsometryEquiv,
    OrthogonalFamily.linear_isometry_apply_dfinsupp_sum_single]
#align
  is_hilbert_sum.linear_isometry_equiv_symm_apply_dfinsupp_sum_single IsHilbertSum.linear_isometry_equiv_symm_apply_dfinsupp_sum_single

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp]
protected theorem IsHilbertSum.linear_isometry_equiv_apply_dfinsupp_sum_single
    (hV : IsHilbertSum 𝕜 E V) (W₀ : Π₀ i : ι, G i) :
    (hV.LinearIsometryEquiv (W₀.Sum fun i => V i) : ∀ i, G i) = W₀ :=
  by
  rw [← hV.linear_isometry_equiv_symm_apply_dfinsupp_sum_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp (config := { contextual := true }) [Dfinsupp.sum, lp.single_apply]
#align
  is_hilbert_sum.linear_isometry_equiv_apply_dfinsupp_sum_single IsHilbertSum.linear_isometry_equiv_apply_dfinsupp_sum_single

/-- Given a total orthonormal family `v : ι → E`, `E` is a Hilbert sum of `λ i : ι, 𝕜` relative to
the family of linear isometries `λ i, λ k, k • v i`. -/
theorem Orthonormal.isHilbertSum {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) :
    @IsHilbertSum _ 𝕜 _ _ _ _ (fun i : ι => 𝕜) _ fun i =>
      LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  IsHilbertSum.mk hv.OrthogonalFamily
    (by
      convert hsp
      simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_Union])
#align orthonormal.is_hilbert_sum Orthonormal.isHilbertSum

theorem Submodule.isHilbertSumOrthogonal (K : Submodule 𝕜 E) [hK : CompleteSpace K] :
    @IsHilbertSum _ 𝕜 _ E _ _ (fun b => ((cond b K Kᗮ : Submodule 𝕜 E) : Type _)) _ fun b =>
      (cond b K Kᗮ).subtypeₗᵢ :=
  by
  have : ∀ b, CompleteSpace ((cond b K Kᗮ : Submodule 𝕜 E) : Type _) :=
    by
    intro b
    cases b <;> first |exact orthogonal.complete_space K|assumption
  refine' IsHilbertSum.mkInternal _ K.orthogonal_family_self _
  refine' le_trans _ (Submodule.le_topological_closure _)
  rw [supᵢ_bool_eq, cond, cond]
  refine' Codisjoint.top_le _
  exact submodule.is_compl_orthogonal_of_complete_space.codisjoint
#align submodule.is_hilbert_sum_orthogonal Submodule.isHilbertSumOrthogonal

end IsHilbertSum

/-! ### Hilbert bases -/


section

variable (ι) (𝕜) (E)

/-- A Hilbert basis on `ι` for an inner product space `E` is an identification of `E` with the `lp`
space `ℓ²(ι, 𝕜)`. -/
structure HilbertBasis where of_repr ::
  repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜)
#align hilbert_basis HilbertBasis

end

namespace HilbertBasis

instance {ι : Type _} : Inhabited (HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) :=
  ⟨of_repr (LinearIsometryEquiv.refl 𝕜 _)⟩

/-- `b i` is the `i`th basis vector. -/
instance : CoeFun (HilbertBasis ι 𝕜 E) fun _ => ι → E
    where coe b i := b.repr.symm (lp.single 2 i (1 : 𝕜))

@[simp]
protected theorem repr_symm_single (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (lp.single 2 i (1 : 𝕜)) = b i :=
  rfl
#align hilbert_basis.repr_symm_single HilbertBasis.repr_symm_single

@[simp]
protected theorem repr_self (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = lp.single 2 i (1 : 𝕜) := by
  rw [← b.repr_symm_single, LinearIsometryEquiv.apply_symm_apply]
#align hilbert_basis.repr_self HilbertBasis.repr_self

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `repr_apply_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b] [":" (Term.app `HilbertBasis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder "(" [`v] [":" `E] [] ")")
        (Term.explicitBinder "(" [`i] [":" `ι] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj `b "." `repr) [`v `i])
         "="
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `v "⟫"))))
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
               [(patternIgnore (token.«← » "←"))]
               (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v]))
              ","
              (Tactic.rwRule [] `b.repr_self)
              ","
              (Tactic.rwRule [] `lp.inner_single_left)]
             "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] [] [])])))
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
              [(patternIgnore (token.«← » "←"))]
              (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v]))
             ","
             (Tactic.rwRule [] `b.repr_self)
             ","
             (Tactic.rwRule [] `lp.inner_single_left)]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v]))
         ","
         (Tactic.rwRule [] `b.repr_self)
         ","
         (Tactic.rwRule [] `lp.inner_single_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lp.inner_single_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b.repr_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b.repr.inner_map_map [(Term.app `b [`i]) `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `b [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `b [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.repr.inner_map_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj `b "." `repr) [`v `i])
       "="
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `v "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `v "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    repr_apply_apply
    ( b : HilbertBasis ι 𝕜 E ) ( v : E ) ( i : ι ) : b . repr v i = ⟪ b i , v ⟫
    := by rw [ ← b.repr.inner_map_map b i v , b.repr_self , lp.inner_single_left ] simp
#align hilbert_basis.repr_apply_apply HilbertBasis.repr_apply_apply

@[simp]
protected theorem orthonormal (b : HilbertBasis ι 𝕜 E) : Orthonormal 𝕜 b :=
  by
  rw [orthonormal_iff_ite]
  intro i j
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self, b.repr_self, lp.inner_single_left,
    lp.single_apply]
  simp
#align hilbert_basis.orthonormal HilbertBasis.orthonormal

protected theorem has_sum_repr_symm (b : HilbertBasis ι 𝕜 E) (f : ℓ²(ι, 𝕜)) :
    HasSum (fun i => f i • b i) (b.repr.symm f) :=
  by
  suffices H :
    (fun i : ι => f i • b i) = fun b_1 : ι =>
      b.repr.symm.to_continuous_linear_equiv ((fun i : ι => lp.single 2 i (f i)) b_1)
  · rw [H]
    have : HasSum (fun i : ι => lp.single 2 i (f i)) f := lp.has_sum_single Ennreal.two_ne_top f
    exact (↑b.repr.symm.to_continuous_linear_equiv : ℓ²(ι, 𝕜) →L[𝕜] E).HasSum this
  ext i
  apply b.repr.injective
  have : lp.single 2 i (f i * 1) = f i • lp.single 2 i 1 := lp.single_smul 2 i (1 : 𝕜) (f i)
  rw [mul_one] at this
  rw [LinearIsometryEquiv.map_smul, b.repr_self, ← this,
    LinearIsometryEquiv.coe_to_continuous_linear_equiv]
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm
#align hilbert_basis.has_sum_repr_symm HilbertBasis.has_sum_repr_symm

protected theorem has_sum_repr (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => b.repr x i • b i) x := by simpa using b.has_sum_repr_symm (b.repr x)
#align hilbert_basis.has_sum_repr HilbertBasis.has_sum_repr

@[simp]
protected theorem dense_span (b : HilbertBasis ι 𝕜 E) :
    (span 𝕜 (Set.range b)).topologicalClosure = ⊤ := by
  classical
    rw [eq_top_iff]
    rintro x -
    refine' mem_closure_of_tendsto (b.has_sum_repr x) (eventually_of_forall _)
    intro s
    simp only [SetLike.mem_coe]
    refine' sum_mem _
    rintro i -
    refine' smul_mem _ _ _
    exact subset_span ⟨i, rfl⟩
#align hilbert_basis.dense_span HilbertBasis.dense_span

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `has_sum_inner_mul_inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b] [":" (Term.app `HilbertBasis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasSum
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            («term_*_»
             (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
             "*"
             (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫"))))
          (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(convert
            "convert"
            []
            (Term.app
             (Term.proj (Term.app `b.has_sum_repr [`y]) "." `mapL)
             [(Term.app `innerSL [`x])])
            [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `innerSL_apply)
              ","
              (Tactic.rwRule [] `b.repr_apply_apply)
              ","
              (Tactic.rwRule [] `inner_smul_right)
              ","
              (Tactic.rwRule [] `mul_comm)]
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
         [(convert
           "convert"
           []
           (Term.app
            (Term.proj (Term.app `b.has_sum_repr [`y]) "." `mapL)
            [(Term.app `innerSL [`x])])
           [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `innerSL_apply)
             ","
             (Tactic.rwRule [] `b.repr_apply_apply)
             ","
             (Tactic.rwRule [] `inner_smul_right)
             ","
             (Tactic.rwRule [] `mul_comm)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `innerSL_apply)
         ","
         (Tactic.rwRule [] `b.repr_apply_apply)
         ","
         (Tactic.rwRule [] `inner_smul_right)
         ","
         (Tactic.rwRule [] `mul_comm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_smul_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b.repr_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `innerSL_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app (Term.proj (Term.app `b.has_sum_repr [`y]) "." `mapL) [(Term.app `innerSL [`x])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `b.has_sum_repr [`y]) "." `mapL) [(Term.app `innerSL [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `innerSL [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `innerSL
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `innerSL [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `b.has_sum_repr [`y]) "." `mapL)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `b.has_sum_repr [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.has_sum_repr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `b.has_sum_repr [`y]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasSum
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          («term_*_»
           (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
           "*"
           (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫"))))
        (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    has_sum_inner_mul_inner
    ( b : HilbertBasis ι 𝕜 E ) ( x y : E ) : HasSum fun i => ⟪ x , b i ⟫ * ⟪ b i , y ⟫ ⟪ x , y ⟫
    :=
      by
        convert b.has_sum_repr y . mapL innerSL x
          ext i
          rw [ innerSL_apply , b.repr_apply_apply , inner_smul_right , mul_comm ]
#align hilbert_basis.has_sum_inner_mul_inner HilbertBasis.has_sum_inner_mul_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `summable_inner_mul_inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b] [":" (Term.app `HilbertBasis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Summable
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            («term_*_»
             (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
             "*"
             (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
              "⟪"
              (Term.app `b [`i])
              ", "
              `y
              "⟫"))))])))
      (Command.declValSimple
       ":="
       (Term.proj (Term.app (Term.proj `b "." `has_sum_inner_mul_inner) [`x `y]) "." `Summable)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app (Term.proj `b "." `has_sum_inner_mul_inner) [`x `y]) "." `Summable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `b "." `has_sum_inner_mul_inner) [`x `y])
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
      (Term.proj `b "." `has_sum_inner_mul_inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `b "." `has_sum_inner_mul_inner) [`x `y])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          («term_*_»
           (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
           "*"
           (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        («term_*_»
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
         "*"
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
       "*"
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    summable_inner_mul_inner
    ( b : HilbertBasis ι 𝕜 E ) ( x y : E ) : Summable fun i => ⟪ x , b i ⟫ * ⟪ b i , y ⟫
    := b . has_sum_inner_mul_inner x y . Summable
#align hilbert_basis.summable_inner_mul_inner HilbertBasis.summable_inner_mul_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tsum_inner_mul_inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`b] [":" (Term.app `HilbertBasis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Topology.Algebra.InfiniteSum.«term∑'_,_»
          "∑'"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          («term_*_»
           (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
           "*"
           (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫")))
         "="
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " `y "⟫"))))
      (Command.declValSimple
       ":="
       (Term.proj (Term.app (Term.proj `b "." `has_sum_inner_mul_inner) [`x `y]) "." `tsum_eq)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app (Term.proj `b "." `has_sum_inner_mul_inner) [`x `y]) "." `tsum_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `b "." `has_sum_inner_mul_inner) [`x `y])
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
      (Term.proj `b "." `has_sum_inner_mul_inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `b "." `has_sum_inner_mul_inner) [`x `y])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        («term_*_»
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " (Term.app `b [`i]) "⟫")
         "*"
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" (Term.app `b [`i]) ", " `y "⟫")))
       "="
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    tsum_inner_mul_inner
    ( b : HilbertBasis ι 𝕜 E ) ( x y : E ) : ∑' i , ⟪ x , b i ⟫ * ⟪ b i , y ⟫ = ⟪ x , y ⟫
    := b . has_sum_inner_mul_inner x y . tsum_eq
#align hilbert_basis.tsum_inner_mul_inner HilbertBasis.tsum_inner_mul_inner

-- Note : this should be `b.repr` composed with an identification of `lp (λ i : ι, 𝕜) p` with
-- `pi_Lp p (λ i : ι, 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/-- A finite Hilbert basis is an orthonormal basis. -/
protected def toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) : OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk b.Orthonormal
    (by
      refine' Eq.ge _
      have := (span 𝕜 (finset.univ.image b : Set E)).closed_of_finite_dimensional
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, HilbertBasis.dense_span] using
        this.submodule_topological_closure_eq.symm)
#align hilbert_basis.to_orthonormal_basis HilbertBasis.toOrthonormalBasis

@[simp]
theorem coe_to_orthonormal_basis [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    (b.toOrthonormalBasis : ι → E) = b :=
  OrthonormalBasis.coe_mk _ _
#align hilbert_basis.coe_to_orthonormal_basis HilbertBasis.coe_to_orthonormal_basis

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `has_sum_orthogonal_projection [])
      (Command.declSig
       [(Term.implicitBinder "{" [`U] [":" (Term.app `Submodule [`𝕜 `E])] "}")
        (Term.instBinder "[" [] (Term.app `CompleteSpace [`U]) "]")
        (Term.explicitBinder "(" [`b] [":" (Term.app `HilbertBasis [`ι `𝕜 `U])] [] ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasSum
         [(Term.fun
           "fun"
           (Term.basicFun
            [`i]
            []
            "=>"
            (Algebra.Group.Defs.«term_•_»
             (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
              "⟪"
              (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
              ", "
              `x
              "⟫")
             " • "
             (Term.app `b [`i]))))
          (Term.app `orthogonalProjection [`U `x])])))
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
               [(Tactic.simpLemma [] [] `b.repr_apply_apply)
                ","
                (Tactic.simpLemma [] [] `inner_orthogonal_projection_eq_of_mem_left)]
               "]")]
             ["using" (Term.app `b.has_sum_repr [(Term.app `orthogonalProjection [`U `x])])]))])))
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
              [(Tactic.simpLemma [] [] `b.repr_apply_apply)
               ","
               (Tactic.simpLemma [] [] `inner_orthogonal_projection_eq_of_mem_left)]
              "]")]
            ["using" (Term.app `b.has_sum_repr [(Term.app `orthogonalProjection [`U `x])])]))])))
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
          [(Tactic.simpLemma [] [] `b.repr_apply_apply)
           ","
           (Tactic.simpLemma [] [] `inner_orthogonal_projection_eq_of_mem_left)]
          "]")]
        ["using" (Term.app `b.has_sum_repr [(Term.app `orthogonalProjection [`U `x])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b.has_sum_repr [(Term.app `orthogonalProjection [`U `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `orthogonalProjection [`U `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `orthogonalProjection
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `orthogonalProjection [`U `x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b.has_sum_repr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_orthogonal_projection_eq_of_mem_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b.repr_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasSum
       [(Term.fun
         "fun"
         (Term.basicFun
          [`i]
          []
          "=>"
          (Algebra.Group.Defs.«term_•_»
           (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
            "⟪"
            (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
            ", "
            `x
            "⟫")
           " • "
           (Term.app `b [`i]))))
        (Term.app `orthogonalProjection [`U `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `orthogonalProjection [`U `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `orthogonalProjection
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `orthogonalProjection [`U `x])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
        []
        "=>"
        (Algebra.Group.Defs.«term_•_»
         (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
          "⟪"
          (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
          ", "
          `x
          "⟫")
         " • "
         (Term.app `b [`i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
        "⟪"
        (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
        ", "
        `x
        "⟫")
       " • "
       (Term.app `b [`i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `b [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»
       "⟪"
       (Term.typeAscription "(" (Term.app `b [`i]) ":" [`E] ")")
       ", "
       `x
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.L2Space.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.L2Space.term⟪_,_⟫._@.Analysis.InnerProductSpace.L2Space._hyg.17'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    has_sum_orthogonal_projection
    { U : Submodule 𝕜 E } [ CompleteSpace U ] ( b : HilbertBasis ι 𝕜 U ) ( x : E )
      : HasSum fun i => ⟪ ( b i : E ) , x ⟫ • b i orthogonalProjection U x
    :=
      by
        simpa
          only
            [ b.repr_apply_apply , inner_orthogonal_projection_eq_of_mem_left ]
            using b.has_sum_repr orthogonalProjection U x
#align hilbert_basis.has_sum_orthogonal_projection HilbertBasis.has_sum_orthogonal_projection

theorem finite_spans_dense (b : HilbertBasis ι 𝕜 E) :
    (⨆ J : Finset ι, span 𝕜 (J.image b : Set E)).topologicalClosure = ⊤ :=
  eq_top_iff.mpr <|
    b.dense_span.ge.trans
      (by
        simp_rw [← Submodule.span_Union]
        exact
          topological_closure_mono
            (span_mono <|
              set.range_subset_iff.mpr fun i =>
                Set.mem_unionᵢ_of_mem {i} <|
                  finset.mem_coe.mpr <| Finset.mem_image_of_mem _ <| Finset.mem_singleton_self i))
#align hilbert_basis.finite_spans_dense HilbertBasis.finite_spans_dense

variable {v : ι → E} (hv : Orthonormal 𝕜 v)

include hv cplt

/-- An orthonormal family of vectors whose span is dense in the whole module is a Hilbert basis. -/
protected def mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.of_repr <| (hv.IsHilbertSum hsp).LinearIsometryEquiv
#align hilbert_basis.mk HilbertBasis.mk

theorem Orthonormal.linear_isometry_equiv_symm_apply_single_one (h i) :
    (hv.IsHilbertSum h).LinearIsometryEquiv.symm (lp.single 2 i 1) = v i := by
  rw [IsHilbertSum.linear_isometry_equiv_symm_apply_single, LinearIsometry.to_span_singleton_apply,
    one_smul]
#align
  orthonormal.linear_isometry_equiv_symm_apply_single_one Orthonormal.linear_isometry_equiv_symm_apply_single_one

@[simp]
protected theorem coe_mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) :
    ⇑(HilbertBasis.mk hv hsp) = v := by
  apply funext <| Orthonormal.linear_isometry_equiv_symm_apply_single_one hv hsp
#align hilbert_basis.coe_mk HilbertBasis.coe_mk

/-- An orthonormal family of vectors whose span has trivial orthogonal complement is a Hilbert
basis. -/
protected def mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk hv
    (by rw [← orthogonal_orthogonal_eq_closure, ← eq_top_iff, orthogonal_eq_top_iff, hsp])
#align hilbert_basis.mk_of_orthogonal_eq_bot HilbertBasis.mkOfOrthogonalEqBot

@[simp]
protected theorem coe_of_orthogonal_eq_bot_mk (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    ⇑(HilbertBasis.mkOfOrthogonalEqBot hv hsp) = v :=
  HilbertBasis.coe_mk hv _
#align hilbert_basis.coe_of_orthogonal_eq_bot_mk HilbertBasis.coe_of_orthogonal_eq_bot_mk

omit hv

-- Note : this should be `b.repr` composed with an identification of `lp (λ i : ι, 𝕜) p` with
-- `pi_Lp p (λ i : ι, 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/-- An orthonormal basis is an Hilbert basis. -/
protected def OrthonormalBasis.toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk b.Orthonormal <| by
    simpa only [← OrthonormalBasis.coe_to_basis, b.to_basis.span_eq, eq_top_iff] using
      @subset_closure E _ _
#align orthonormal_basis.to_hilbert_basis OrthonormalBasis.toHilbertBasis

@[simp]
theorem OrthonormalBasis.coe_to_hilbert_basis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    (b.toHilbertBasis : ι → E) = b :=
  HilbertBasis.coe_mk _ _
#align orthonormal_basis.coe_to_hilbert_basis OrthonormalBasis.coe_to_hilbert_basis

/-- A Hilbert space admits a Hilbert basis extending a given orthonormal subset. -/
theorem Orthonormal.exists_hilbert_basis_extension {s : Set E} (hs : Orthonormal 𝕜 (coe : s → E)) :
    ∃ (w : Set E)(b : HilbertBasis w 𝕜 E), s ⊆ w ∧ ⇑b = (coe : w → E) :=
  let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs
  ⟨w,
    HilbertBasis.mkOfOrthogonalEqBot hw_ortho
      (by simpa [maximal_orthonormal_iff_orthogonal_complement_eq_bot hw_ortho] using hw_max),
    hws, HilbertBasis.coe_of_orthogonal_eq_bot_mk _ _⟩
#align orthonormal.exists_hilbert_basis_extension Orthonormal.exists_hilbert_basis_extension

variable (𝕜 E)

/-- A Hilbert space admits a Hilbert basis. -/
theorem exists_hilbert_basis : ∃ (w : Set E)(b : HilbertBasis w 𝕜 E), ⇑b = (coe : w → E) :=
  let ⟨w, hw, hw', hw''⟩ := (orthonormalEmpty 𝕜 E).exists_hilbert_basis_extension
  ⟨w, hw, hw''⟩
#align exists_hilbert_basis exists_hilbert_basis

end HilbertBasis

