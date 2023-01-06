/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module topology.gluing
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.GlueData
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise
import Mathbin.Topology.Category.TopCat.Limits
import Mathbin.Topology.Category.TopCat.Opens

/-!
# Gluing Topological spaces

Given a family of gluing data (see `category_theory/glue_data`), we can then glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.glue_data`: A structure containing the family of gluing data.
* `category_theory.glue_data.glued`: The glued topological space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `category_theory.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : ι`.
* `Top.glue_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `t i j x = y`. See `Top.glue_data.ι_eq_iff_rel`.
* `Top.glue_data.mk`: A constructor of `glue_data` whose conditions are stated in terms of
  elements rather than subobjects and pullbacks.
* `Top.glue_data.of_open_subsets`: Given a family of open sets, we may glue them into a new
  topological space. This new space embeds into the original space, and is homeomorphic to it if
  the given family is an open cover (`Top.glue_data.open_cover_glue_homeo`).

## Main results

* `Top.glue_data.is_open_iff`: A set in `glued` is open iff its preimage along each `ι i` is
    open.
* `Top.glue_data.ι_jointly_surjective`: The `ι i`s are jointly surjective.
* `Top.glue_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.glue_data.ι_eq_iff_rel`: `ι i x = ι j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.glue_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.glue_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.glue_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.glue_data.ι_open_embedding`: Each of the `ι i`s are open embeddings.

-/


noncomputable section

open TopologicalSpace CategoryTheory

universe v u

open CategoryTheory.Limits

namespace TopCat

/-- A family of gluing data consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
  (Note that this is `J × J → Top` rather than `J → J → Top` to connect to the
  limits library easier.)
4. An open embedding `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
    (This merely means that `V i j ∩ V i k ⊆ t i j ⁻¹' (V j i ∩ V j k)`.)
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.

Most of the times it would be easier to use the constructor `Top.glue_data.mk'` where the conditions
are stated in a less categorical way.
-/
@[nolint has_nonempty_instance]
structure GlueData extends GlueData TopCat where
  f_open : ∀ i j, OpenEmbedding (f i j)
  f_mono := fun i j => (TopCat.mono_iff_injective _).mpr (f_open i j).toEmbedding.inj
#align Top.glue_data TopCat.GlueData

namespace GlueData

variable (D : GlueData.{u})

-- mathport name: «expr𝖣»
local notation "𝖣" => D.toGlueData

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `π_surjective [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Function.Surjective
         [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `π)])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (Term.app
          `TopCat.epi_iff_surjective
          [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `π)])
         "."
         `mp)
        [`inferInstance])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `TopCat.epi_iff_surjective
         [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `π)])
        "."
        `mp)
       [`inferInstance])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `TopCat.epi_iff_surjective
        [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `π)])
       "."
       `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `TopCat.epi_iff_surjective
       [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `π)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `π)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
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
  π_surjective
  : Function.Surjective 𝖣 . π
  := TopCat.epi_iff_surjective 𝖣 . π . mp inferInstance
#align Top.glue_data.π_surjective TopCat.GlueData.π_surjective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `is_open_iff [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`U]
         [":"
          (Term.app `Set [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `glued)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Term.app `IsOpen [`U])
         "↔"
         (Term.forall
          "∀"
          [`i]
          []
          ","
          (Term.app
           `IsOpen
           [(Set.Data.Set.Image.«term_⁻¹'_»
             (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
             " ⁻¹' "
             `U)])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.delta "delta" [`CategoryTheory.GlueData.ι] [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `multicoequalizer.ι_sigma_π
                [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)]))]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (Term.app
                 `homeo_of_iso
                 [(Term.proj
                   (Term.app
                    `multicoequalizer.iso_coequalizer
                    [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
                   "."
                   `symm)])
                "."
                `is_open_preimage))]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `coequalizer_is_open_iff)
              ","
              (Tactic.rwRule [] (Term.explicitUniv `colimit_is_open_iff ".{" [`u] "}"))]
             "]")
            [])
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`h `j])
             []
             (Tactic.exact "exact" (Term.app `h [(Term.anonymousCtor "⟨" [`j] "⟩")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`h `j])
             []
             (Tactic.cases "cases" [(Tactic.casesTarget [] `j)] [] [])
             []
             (Tactic.exact "exact" (Term.app `h [`j]))])])))
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
         [(Tactic.delta "delta" [`CategoryTheory.GlueData.ι] [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `multicoequalizer.ι_sigma_π
               [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)]))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.app
                `homeo_of_iso
                [(Term.proj
                  (Term.app
                   `multicoequalizer.iso_coequalizer
                   [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
                  "."
                  `symm)])
               "."
               `is_open_preimage))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `coequalizer_is_open_iff)
             ","
             (Tactic.rwRule [] (Term.explicitUniv `colimit_is_open_iff ".{" [`u] "}"))]
            "]")
           [])
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`h `j])
            []
            (Tactic.exact "exact" (Term.app `h [(Term.anonymousCtor "⟨" [`j] "⟩")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`h `j])
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `j)] [] [])
            []
            (Tactic.exact "exact" (Term.app `h [`j]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`h `j])
        []
        (Tactic.cases "cases" [(Tactic.casesTarget [] `j)] [] [])
        []
        (Tactic.exact "exact" (Term.app `h [`j]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `h [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `j)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h `j])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`h `j])
        []
        (Tactic.exact "exact" (Term.app `h [(Term.anonymousCtor "⟨" [`j] "⟩")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `h [(Term.anonymousCtor "⟨" [`j] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [(Term.anonymousCtor "⟨" [`j] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`j] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h `j])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `coequalizer_is_open_iff)
         ","
         (Tactic.rwRule [] (Term.explicitUniv `colimit_is_open_iff ".{" [`u] "}"))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.explicitUniv `colimit_is_open_iff ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `colimit_is_open_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coequalizer_is_open_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (Term.app
            `homeo_of_iso
            [(Term.proj
              (Term.app
               `multicoequalizer.iso_coequalizer
               [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
              "."
              `symm)])
           "."
           `is_open_preimage))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `homeo_of_iso
        [(Term.proj
          (Term.app
           `multicoequalizer.iso_coequalizer
           [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
          "."
          `symm)])
       "."
       `is_open_preimage)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `homeo_of_iso
       [(Term.proj
         (Term.app
          `multicoequalizer.iso_coequalizer
          [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
         "."
         `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `multicoequalizer.iso_coequalizer
        [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `multicoequalizer.iso_coequalizer
       [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
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
  is_open_iff
  ( U : Set 𝖣 . glued ) : IsOpen U ↔ ∀ i , IsOpen 𝖣 . ι i ⁻¹' U
  :=
    by
      delta CategoryTheory.GlueData.ι
        simp_rw [ ← multicoequalizer.ι_sigma_π 𝖣 . diagram ]
        rw [ ← homeo_of_iso multicoequalizer.iso_coequalizer 𝖣 . diagram . symm . is_open_preimage ]
        rw [ coequalizer_is_open_iff , colimit_is_open_iff .{ u } ]
        constructor
        · intro h j exact h ⟨ j ⟩
        · intro h j cases j exact h j
#align Top.glue_data.is_open_iff TopCat.GlueData.is_open_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_jointly_surjective [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `glued)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `y)]
            ":"
            (Term.app (Term.proj `D "." `U) [`i])
            ")")])
         ","
         («term_=_»
          (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i `y])
          "="
          `x))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι_jointly_surjective)
        [(Term.app `forget [`TopCat]) `x])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι_jointly_surjective)
       [(Term.app `forget [`TopCat]) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `forget [`TopCat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `forget [`TopCat]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι_jointly_surjective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
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
  ι_jointly_surjective
  ( x : 𝖣 . glued ) : ∃ ( i : _ ) ( y : D . U i ) , 𝖣 . ι i y = x
  := 𝖣 . ι_jointly_surjective forget TopCat x
#align Top.glue_data.ι_jointly_surjective TopCat.GlueData.ι_jointly_surjective

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `Top.glue_data.ι_eq_iff_rel`.
-/
def Rel (a b : Σi, ((D.U i : TopCat) : Type _)) : Prop :=
  a = b ∨ ∃ x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2
#align Top.glue_data.rel TopCat.GlueData.Rel

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `rel_equiv [])
      (Command.declSig [] (Term.typeSpec ":" (Term.app `Equivalence [(Term.proj `D "." `Rel)])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `Or.inl [(Term.app `refl [`x])])))
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                       [])]
                     "⟩")])
                  [])
                 ")"))]
              [])
             []
             (Std.Tactic.exacts
              "exacts"
              "["
              [(Term.app `Or.inl [`rfl])
               ","
               (Term.app
                `Or.inr
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])
                   ","
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.simp
                        "simp"
                        []
                        []
                        []
                        ["[" [(Tactic.simpLemma [] [] `e₁) "," (Tactic.simpLemma [] [] `e₂)] "]"]
                        [])])))]
                  "⟩")])]
              "]")])))
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                   [])]
                 "⟩"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                   [])]
                 "⟩"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                   [])]
                 "⟩"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                       [])]
                     "⟩")])
                  [])
                 ")"))]
              [])
             []
             (Tactic.exact "exact" `id)
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₃)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₄)])
                       [])]
                     "⟩")])
                  [])
                 ")"))]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app `Or.inr [(Term.anonymousCtor "⟨" [`x "," `e₁ "," `e₂] "⟩")]))
             []
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `z
                []
                []
                ":="
                (Term.app
                 (Term.proj
                  (Term.app
                   `pullback_iso_prod_subtype
                   [(Term.app `D.f [`j `i]) (Term.app `D.f [`j `k])])
                  "."
                  `inv)
                 [(Term.anonymousCtor
                   "⟨"
                   [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                    ","
                    (Term.app `e₂.trans [`e₃.symm])]
                   "⟩")]))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`eq₁ []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app
                    (Term.app `D.t [`j `i])
                    [(Term.app
                      (Term.typeAscription
                       "("
                       `pullback.fst
                       ":"
                       [(Combinatorics.Quiver.Basic.«term_⟶_»
                         (Term.hole "_")
                         " ⟶ "
                         (Term.app `D.V [(Term.hole "_")]))]
                       ")")
                      [`z])])
                   "="
                   `x))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`eq₂ []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app
                    (Term.typeAscription
                     "("
                     `pullback.snd
                     ":"
                     [(Combinatorics.Quiver.Basic.«term_⟶_»
                       (Term.hole "_")
                       " ⟶ "
                       (Term.app `D.V [(Term.hole "_")]))]
                     ")")
                    [`z])
                   "="
                   `y))]
                ":="
                (Term.app
                 `pullback_iso_prod_subtype_inv_snd_apply
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))))
             []
             (Tactic.clearValue "clear_value" [(group `z)])
             []
             (Mathlib.Tactic.tacticRight "right")
             []
             (Mathlib.Tactic.«tacticUse_,,»
              "use"
              [(Term.app
                (Term.typeAscription
                 "("
                 `pullback.fst
                 ":"
                 [(Combinatorics.Quiver.Basic.«term_⟶_»
                   (Term.hole "_")
                   " ⟶ "
                   (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]))]
                 ")")
                [(Term.app `D.t' [(Term.hole "_") (Term.hole "_") (Term.hole "_") `z])])])
             []
             (Tactic.dsimp
              "dsimp"
              []
              []
              ["only"]
              []
              [(Tactic.location "at" (Tactic.locationWildcard "*"))])
             []
             (Mathlib.Tactic.Substs.substs "substs" [`e₁ `e₃ `e₄ `eq₁ `eq₂])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h₁ []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `D.t' [`j `i `k])
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     `pullback.fst
                     " ≫ "
                     (Term.app `D.f [`i `k])))
                   "="
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    `pullback.fst
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `D.t [`j `i])
                     " ≫ "
                     (Term.app `D.f [`i `j])))))]
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
                        (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))]
                      "]")
                     [])
                    []
                    (Tactic.congr "congr" [(num "1")])
                    []
                    (Tactic.exact "exact" `pullback.condition)]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h₂ []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `D.t' [`j `i `k])
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     `pullback.fst
                     " ≫ "
                     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `D.t [`i `k])
                      " ≫ "
                      (Term.app `D.f [`k `i]))))
                   "="
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    `pullback.snd
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `D.t [`j `k])
                     " ≫ "
                     (Term.app `D.f [`k `j])))))]
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
                        (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))]
                      "]")
                     [])
                    []
                    (Tactic.apply
                     "apply"
                     (Term.app
                      (Term.explicit "@" `epi.left_cancellation)
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.hole "_")
                       (Term.hole "_")
                       (Term.app `D.t' [`k `j `i])]))
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.proj
                         (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
                         "."
                         `cocycle_assoc))
                       ","
                       (Tactic.rwRule
                        []
                        (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))
                       ","
                       (Tactic.rwRule
                        []
                        (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
                      "]")
                     [])
                    []
                    (Tactic.exact "exact" `pullback.condition.symm)]))))))
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `ContinuousMap.congr_fun [`h₁ `z])
                ","
                (Term.app `ContinuousMap.congr_fun [`h₂ `z])]
               "⟩"))])))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.app `Or.inl [(Term.app `refl [`x])])))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                      [])]
                    "⟩")])
                 [])
                ")"))]
             [])
            []
            (Std.Tactic.exacts
             "exacts"
             "["
             [(Term.app `Or.inl [`rfl])
              ","
              (Term.app
               `Or.inr
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["[" [(Tactic.simpLemma [] [] `e₁) "," (Tactic.simpLemma [] [] `e₂)] "]"]
                       [])])))]
                 "⟩")])]
             "]")])))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                      [])]
                    "⟩")])
                 [])
                ")"))]
             [])
            []
            (Tactic.exact "exact" `id)
            []
            (Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₃)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₄)])
                      [])]
                    "⟩")])
                 [])
                ")"))]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app `Or.inr [(Term.anonymousCtor "⟨" [`x "," `e₁ "," `e₂] "⟩")]))
            []
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `z
               []
               []
               ":="
               (Term.app
                (Term.proj
                 (Term.app
                  `pullback_iso_prod_subtype
                  [(Term.app `D.f [`j `i]) (Term.app `D.f [`j `k])])
                 "."
                 `inv)
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                   ","
                   (Term.app `e₂.trans [`e₃.symm])]
                  "⟩")]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`eq₁ []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app
                   (Term.app `D.t [`j `i])
                   [(Term.app
                     (Term.typeAscription
                      "("
                      `pullback.fst
                      ":"
                      [(Combinatorics.Quiver.Basic.«term_⟶_»
                        (Term.hole "_")
                        " ⟶ "
                        (Term.app `D.V [(Term.hole "_")]))]
                      ")")
                     [`z])])
                  "="
                  `x))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`eq₂ []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.app
                   (Term.typeAscription
                    "("
                    `pullback.snd
                    ":"
                    [(Combinatorics.Quiver.Basic.«term_⟶_»
                      (Term.hole "_")
                      " ⟶ "
                      (Term.app `D.V [(Term.hole "_")]))]
                    ")")
                   [`z])
                  "="
                  `y))]
               ":="
               (Term.app
                `pullback_iso_prod_subtype_inv_snd_apply
                [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))))
            []
            (Tactic.clearValue "clear_value" [(group `z)])
            []
            (Mathlib.Tactic.tacticRight "right")
            []
            (Mathlib.Tactic.«tacticUse_,,»
             "use"
             [(Term.app
               (Term.typeAscription
                "("
                `pullback.fst
                ":"
                [(Combinatorics.Quiver.Basic.«term_⟶_»
                  (Term.hole "_")
                  " ⟶ "
                  (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]))]
                ")")
               [(Term.app `D.t' [(Term.hole "_") (Term.hole "_") (Term.hole "_") `z])])])
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             ["only"]
             []
             [(Tactic.location "at" (Tactic.locationWildcard "*"))])
            []
            (Mathlib.Tactic.Substs.substs "substs" [`e₁ `e₃ `e₄ `eq₁ `eq₂])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h₁ []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `D.t' [`j `i `k])
                   " ≫ "
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    `pullback.fst
                    " ≫ "
                    (Term.app `D.f [`i `k])))
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   `pullback.fst
                   " ≫ "
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `D.t [`j `i])
                    " ≫ "
                    (Term.app `D.f [`i `j])))))]
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
                       (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))]
                     "]")
                    [])
                   []
                   (Tactic.congr "congr" [(num "1")])
                   []
                   (Tactic.exact "exact" `pullback.condition)]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h₂ []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `D.t' [`j `i `k])
                   " ≫ "
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    `pullback.fst
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `D.t [`i `k])
                     " ≫ "
                     (Term.app `D.f [`k `i]))))
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   `pullback.snd
                   " ≫ "
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `D.t [`j `k])
                    " ≫ "
                    (Term.app `D.f [`k `j])))))]
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
                       (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))]
                     "]")
                    [])
                   []
                   (Tactic.apply
                    "apply"
                    (Term.app
                     (Term.explicit "@" `epi.left_cancellation)
                     [(Term.hole "_")
                      (Term.hole "_")
                      (Term.hole "_")
                      (Term.hole "_")
                      (Term.app `D.t' [`k `j `i])]))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       []
                       (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `cocycle_assoc))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
                     "]")
                    [])
                   []
                   (Tactic.exact "exact" `pullback.condition.symm)]))))))
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `ContinuousMap.congr_fun [`h₁ `z])
               ","
               (Term.app `ContinuousMap.congr_fun [`h₂ `z])]
              "⟩"))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `c)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.paren
              "("
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                    [])]
                  "⟩")
                 "|"
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                    [])]
                  "⟩")])
               [])
              ")"))]
           [])
          []
          (Tactic.exact "exact" `id)
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.paren
              "("
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                    [])]
                  "⟩")
                 "|"
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₃)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₄)])
                    [])]
                  "⟩")])
               [])
              ")"))]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `Or.inr [(Term.anonymousCtor "⟨" [`x "," `e₁ "," `e₂] "⟩")]))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `z
             []
             []
             ":="
             (Term.app
              (Term.proj
               (Term.app
                `pullback_iso_prod_subtype
                [(Term.app `D.f [`j `i]) (Term.app `D.f [`j `k])])
               "."
               `inv)
              [(Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
                 ","
                 (Term.app `e₂.trans [`e₃.symm])]
                "⟩")]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`eq₁ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 (Term.app `D.t [`j `i])
                 [(Term.app
                   (Term.typeAscription
                    "("
                    `pullback.fst
                    ":"
                    [(Combinatorics.Quiver.Basic.«term_⟶_»
                      (Term.hole "_")
                      " ⟶ "
                      (Term.app `D.V [(Term.hole "_")]))]
                    ")")
                   [`z])])
                "="
                `x))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`eq₂ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 (Term.typeAscription
                  "("
                  `pullback.snd
                  ":"
                  [(Combinatorics.Quiver.Basic.«term_⟶_»
                    (Term.hole "_")
                    " ⟶ "
                    (Term.app `D.V [(Term.hole "_")]))]
                  ")")
                 [`z])
                "="
                `y))]
             ":="
             (Term.app
              `pullback_iso_prod_subtype_inv_snd_apply
              [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))))
          []
          (Tactic.clearValue "clear_value" [(group `z)])
          []
          (Mathlib.Tactic.tacticRight "right")
          []
          (Mathlib.Tactic.«tacticUse_,,»
           "use"
           [(Term.app
             (Term.typeAscription
              "("
              `pullback.fst
              ":"
              [(Combinatorics.Quiver.Basic.«term_⟶_»
                (Term.hole "_")
                " ⟶ "
                (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]))]
              ")")
             [(Term.app `D.t' [(Term.hole "_") (Term.hole "_") (Term.hole "_") `z])])])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           []
           [(Tactic.location "at" (Tactic.locationWildcard "*"))])
          []
          (Mathlib.Tactic.Substs.substs "substs" [`e₁ `e₃ `e₄ `eq₁ `eq₂])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₁ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `D.t' [`j `i `k])
                 " ≫ "
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  `pullback.fst
                  " ≫ "
                  (Term.app `D.f [`i `k])))
                "="
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 `pullback.fst
                 " ≫ "
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `D.t [`j `i])
                  " ≫ "
                  (Term.app `D.f [`i `j])))))]
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
                     (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))]
                   "]")
                  [])
                 []
                 (Tactic.congr "congr" [(num "1")])
                 []
                 (Tactic.exact "exact" `pullback.condition)]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `D.t' [`j `i `k])
                 " ≫ "
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  `pullback.fst
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `D.t [`i `k])
                   " ≫ "
                   (Term.app `D.f [`k `i]))))
                "="
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 `pullback.snd
                 " ≫ "
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `D.t [`j `k])
                  " ≫ "
                  (Term.app `D.f [`k `j])))))]
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
                     (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))]
                   "]")
                  [])
                 []
                 (Tactic.apply
                  "apply"
                  (Term.app
                   (Term.explicit "@" `epi.left_cancellation)
                   [(Term.hole "_")
                    (Term.hole "_")
                    (Term.hole "_")
                    (Term.hole "_")
                    (Term.app `D.t' [`k `j `i])]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `cocycle_assoc))
                    ","
                    (Tactic.rwRule
                     []
                     (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))
                    ","
                    (Tactic.rwRule
                     []
                     (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
                   "]")
                  [])
                 []
                 (Tactic.exact "exact" `pullback.condition.symm)]))))))
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.app `ContinuousMap.congr_fun [`h₁ `z])
             ","
             (Term.app `ContinuousMap.congr_fun [`h₂ `z])]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `ContinuousMap.congr_fun [`h₁ `z])
         ","
         (Term.app `ContinuousMap.congr_fun [`h₂ `z])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `ContinuousMap.congr_fun [`h₁ `z])
        ","
        (Term.app `ContinuousMap.congr_fun [`h₂ `z])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ContinuousMap.congr_fun [`h₂ `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousMap.congr_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ContinuousMap.congr_fun [`h₁ `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousMap.congr_fun
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₂ []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `D.t' [`j `i `k])
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              `pullback.fst
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.t [`i `k])
               " ≫ "
               (Term.app `D.f [`k `i]))))
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             `pullback.snd
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `D.t [`j `k])
              " ≫ "
              (Term.app `D.f [`k `j])))))]
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
                 (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))]
               "]")
              [])
             []
             (Tactic.apply
              "apply"
              (Term.app
               (Term.explicit "@" `epi.left_cancellation)
               [(Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.app `D.t' [`k `j `i])]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `cocycle_assoc))
                ","
                (Tactic.rwRule
                 []
                 (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))
                ","
                (Tactic.rwRule
                 []
                 (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
               "]")
              [])
             []
             (Tactic.exact "exact" `pullback.condition.symm)]))))))
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
              (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))]
            "]")
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            (Term.explicit "@" `epi.left_cancellation)
            [(Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.app `D.t' [`k `j `i])]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `cocycle_assoc))
             ","
             (Tactic.rwRule
              []
              (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))
             ","
             (Tactic.rwRule
              []
              (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
            "]")
           [])
          []
          (Tactic.exact "exact" `pullback.condition.symm)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `pullback.condition.symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pullback.condition.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `cocycle_assoc))
         ","
         (Tactic.rwRule
          []
          (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_fac_assoc))
         ","
         (Tactic.rwRule
          []
          (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
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
  rel_equiv
  : Equivalence D . Rel
  :=
    ⟨
      fun x => Or.inl refl x
        ,
        by
          rintro a b ( ⟨ ⟨ ⟩ ⟩ | ⟨ x , e₁ , e₂ ⟩ )
            exacts [ Or.inl rfl , Or.inr ⟨ D.t _ _ x , by simp [ e₁ , e₂ ] ⟩ ]
        ,
        by
          rintro ⟨ i , a ⟩ ⟨ j , b ⟩ ⟨ k , c ⟩ ( ⟨ ⟨ ⟩ ⟩ | ⟨ x , e₁ , e₂ ⟩ )
            exact id
            rintro ( ⟨ ⟨ ⟩ ⟩ | ⟨ y , e₃ , e₄ ⟩ )
            exact Or.inr ⟨ x , e₁ , e₂ ⟩
            let
              z := pullback_iso_prod_subtype D.f j i D.f j k . inv ⟨ ⟨ _ , _ ⟩ , e₂.trans e₃.symm ⟩
            have eq₁ : D.t j i ( pullback.fst : _ ⟶ D.V _ ) z = x := by simp
            have
              eq₂
                : ( pullback.snd : _ ⟶ D.V _ ) z = y
                :=
                pullback_iso_prod_subtype_inv_snd_apply _ _ _
            clear_value z
            right
            use ( pullback.fst : _ ⟶ D.V ( i , k ) ) D.t' _ _ _ z
            dsimp only at *
            substs e₁ e₃ e₄ eq₁ eq₂
            have
              h₁
                : D.t' j i k ≫ pullback.fst ≫ D.f i k = pullback.fst ≫ D.t j i ≫ D.f i j
                :=
                by rw [ ← 𝖣 . t_fac_assoc ] congr 1 exact pullback.condition
            have
              h₂
                : D.t' j i k ≫ pullback.fst ≫ D.t i k ≫ D.f k i = pullback.snd ≫ D.t j k ≫ D.f k j
                :=
                by
                  rw [ ← 𝖣 . t_fac_assoc ]
                    apply @ epi.left_cancellation _ _ _ _ D.t' k j i
                    rw [ 𝖣 . cocycle_assoc , 𝖣 . t_fac_assoc , 𝖣 . t_inv_assoc ]
                    exact pullback.condition.symm
            exact ⟨ ContinuousMap.congr_fun h₁ z , ContinuousMap.congr_fun h₂ z ⟩
      ⟩
#align Top.glue_data.rel_equiv TopCat.GlueData.rel_equiv

open CategoryTheory.Limits.WalkingParallelPair

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eqv_gen_of_π_eq [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`x `y]
         [":"
          (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Products.«term∐_»
           "∐ "
           (Term.proj `D "." `U))]
         "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `π) [`x])
           "="
           (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `π) [`y]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `EqvGen
         [(Term.app
           `Types.CoequalizerRel
           [(Term.proj
             (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
             "."
             `fstSigmaMap)
            (Term.proj
             (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
             "."
             `sndSigmaMap)])
          `x
          `y])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.delta
            "delta"
            [`glue_data.π `multicoequalizer.sigma_π]
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_app)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Mathlib.Tactic.tacticReplace_
            "replace"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h []]
              []
              ":="
              (Term.app
               (Term.proj
                (Term.app
                 `TopCat.mono_iff_injective
                 [(Term.proj
                   (Term.app
                    `multicoequalizer.iso_coequalizer
                    [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
                   "."
                   `inv)])
                "."
                `mp)
               [(Term.hole "_") `h]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `diagram
              []
              []
              ":="
              (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
               (Term.app
                `parallel_pair
                [(Term.proj
                  (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
                  "."
                  `fstSigmaMap)
                 (Term.proj
                  (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
                  "."
                  `sndSigmaMap)])
               " ⋙ "
               (Term.app `forget [(Term.hole "_")])))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app `colimit.ι [`diagram `one `x])
                 "="
                 (Term.app `colimit.ι [`diagram `one `y])))]
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
                      `ι_preserves_colimits_iso_hom)]
                    "]")
                   [])
                  []
                  (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `colimit.ι [`diagram (Term.hole "_")])
                   " ≫ "
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `colim.map [(Term.hole "_")])
                    " ≫ "
                    (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
                  [(Term.hole "_")])
                 "="
                 (Term.app
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `colimit.ι [`diagram (Term.hole "_")])
                   " ≫ "
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app `colim.map [(Term.hole "_")])
                    " ≫ "
                    (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
                  [(Term.hole "_")])))]
              ":="
              (Term.typeAscription
               "("
               (Term.app
                `congr_arg
                [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app
                   `colim.map
                   [(Term.proj (Term.app `diagram_iso_parallel_pair [`diagram]) "." `Hom)])
                  " ≫ "
                  (Term.proj
                   (Term.app
                    `colimit.iso_colimit_cocone
                    [(Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])])
                   "."
                   `Hom))
                 `this])
               ":"
               [(Term.hole "_")]
               ")"))))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `eq_to_hom_refl)
              ","
              (Tactic.simpLemma [] [] `types_comp_apply)
              ","
              (Tactic.simpLemma [] [] `colimit.ι_map_assoc)
              ","
              (Tactic.simpLemma [] [] `diagram_iso_parallel_pair_hom_app)
              ","
              (Tactic.simpLemma [] [] `colimit.iso_colimit_cocone_ι_hom)
              ","
              (Tactic.simpLemma [] [] `types_id_apply)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.exact "exact" (Term.app (Term.proj `Quot.eq "." (fieldIdx "1")) [`this]))
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
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
         [(Tactic.delta
           "delta"
           [`glue_data.π `multicoequalizer.sigma_π]
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_app)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             []
             ":="
             (Term.app
              (Term.proj
               (Term.app
                `TopCat.mono_iff_injective
                [(Term.proj
                  (Term.app
                   `multicoequalizer.iso_coequalizer
                   [(Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)])
                  "."
                  `inv)])
               "."
               `mp)
              [(Term.hole "_") `h]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `diagram
             []
             []
             ":="
             (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
              (Term.app
               `parallel_pair
               [(Term.proj
                 (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
                 "."
                 `fstSigmaMap)
                (Term.proj
                 (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
                 "."
                 `sndSigmaMap)])
              " ⋙ "
              (Term.app `forget [(Term.hole "_")])))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app `colimit.ι [`diagram `one `x])
                "="
                (Term.app `colimit.ι [`diagram `one `y])))]
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
                     `ι_preserves_colimits_iso_hom)]
                   "]")
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `colimit.ι [`diagram (Term.hole "_")])
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `colim.map [(Term.hole "_")])
                   " ≫ "
                   (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
                 [(Term.hole "_")])
                "="
                (Term.app
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `colimit.ι [`diagram (Term.hole "_")])
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `colim.map [(Term.hole "_")])
                   " ≫ "
                   (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
                 [(Term.hole "_")])))]
             ":="
             (Term.typeAscription
              "("
              (Term.app
               `congr_arg
               [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app
                  `colim.map
                  [(Term.proj (Term.app `diagram_iso_parallel_pair [`diagram]) "." `Hom)])
                 " ≫ "
                 (Term.proj
                  (Term.app
                   `colimit.iso_colimit_cocone
                   [(Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])])
                  "."
                  `Hom))
                `this])
              ":"
              [(Term.hole "_")]
              ")"))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `eq_to_hom_refl)
             ","
             (Tactic.simpLemma [] [] `types_comp_apply)
             ","
             (Tactic.simpLemma [] [] `colimit.ι_map_assoc)
             ","
             (Tactic.simpLemma [] [] `diagram_iso_parallel_pair_hom_app)
             ","
             (Tactic.simpLemma [] [] `colimit.iso_colimit_cocone_ι_hom)
             ","
             (Tactic.simpLemma [] [] `types_id_apply)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.exact "exact" (Term.app (Term.proj `Quot.eq "." (fieldIdx "1")) [`this]))
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app (Term.proj `Quot.eq "." (fieldIdx "1")) [`this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Quot.eq "." (fieldIdx "1")) [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Quot.eq "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Quot.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
        [(Tactic.simpLemma [] [] `eq_to_hom_refl)
         ","
         (Tactic.simpLemma [] [] `types_comp_apply)
         ","
         (Tactic.simpLemma [] [] `colimit.ι_map_assoc)
         ","
         (Tactic.simpLemma [] [] `diagram_iso_parallel_pair_hom_app)
         ","
         (Tactic.simpLemma [] [] `colimit.iso_colimit_cocone_ι_hom)
         ","
         (Tactic.simpLemma [] [] `types_id_apply)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `types_id_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `colimit.iso_colimit_cocone_ι_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `diagram_iso_parallel_pair_hom_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `colimit.ι_map_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `types_comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_to_hom_refl
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
           («term_=_»
            (Term.app
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `colimit.ι [`diagram (Term.hole "_")])
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `colim.map [(Term.hole "_")])
               " ≫ "
               (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
             [(Term.hole "_")])
            "="
            (Term.app
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `colimit.ι [`diagram (Term.hole "_")])
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `colim.map [(Term.hole "_")])
               " ≫ "
               (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
             [(Term.hole "_")])))]
         ":="
         (Term.typeAscription
          "("
          (Term.app
           `congr_arg
           [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app
              `colim.map
              [(Term.proj (Term.app `diagram_iso_parallel_pair [`diagram]) "." `Hom)])
             " ≫ "
             (Term.proj
              (Term.app
               `colimit.iso_colimit_cocone
               [(Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])])
              "."
              `Hom))
            `this])
          ":"
          [(Term.hole "_")]
          ")"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        `congr_arg
        [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           `colim.map
           [(Term.proj (Term.app `diagram_iso_parallel_pair [`diagram]) "." `Hom)])
          " ≫ "
          (Term.proj
           (Term.app
            `colimit.iso_colimit_cocone
            [(Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])])
           "."
           `Hom))
         `this])
       ":"
       [(Term.hole "_")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          `colim.map
          [(Term.proj (Term.app `diagram_iso_parallel_pair [`diagram]) "." `Hom)])
         " ≫ "
         (Term.proj
          (Term.app
           `colimit.iso_colimit_cocone
           [(Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])])
          "."
          `Hom))
        `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `colim.map [(Term.proj (Term.app `diagram_iso_parallel_pair [`diagram]) "." `Hom)])
       " ≫ "
       (Term.proj
        (Term.app
         `colimit.iso_colimit_cocone
         [(Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])])
        "."
        `Hom))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `colimit.iso_colimit_cocone
        [(Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])])
       "."
       `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `colimit.iso_colimit_cocone
       [(Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])
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
      `types.coequalizer_colimit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colimit.iso_colimit_cocone
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `colimit.iso_colimit_cocone
      [(Term.paren
        "("
        (Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `colim.map [(Term.proj (Term.app `diagram_iso_parallel_pair [`diagram]) "." `Hom)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `diagram_iso_parallel_pair [`diagram]) "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `diagram_iso_parallel_pair [`diagram])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `diagram
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `diagram_iso_parallel_pair
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `diagram_iso_parallel_pair [`diagram])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colim.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app
       `colim.map
       [(Term.proj (Term.paren "(" (Term.app `diagram_iso_parallel_pair [`diagram]) ")") "." `Hom)])
      " ≫ "
      (Term.proj
       (Term.paren
        "("
        (Term.app
         `colimit.iso_colimit_cocone
         [(Term.paren
           "("
           (Term.app `types.coequalizer_colimit [(Term.hole "_") (Term.hole "_")])
           ")")])
        ")")
       "."
       `Hom))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `colimit.ι [`diagram (Term.hole "_")])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `colim.map [(Term.hole "_")])
          " ≫ "
          (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
        [(Term.hole "_")])
       "="
       (Term.app
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `colimit.ι [`diagram (Term.hole "_")])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `colim.map [(Term.hole "_")])
          " ≫ "
          (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `colimit.ι [`diagram (Term.hole "_")])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `colim.map [(Term.hole "_")])
         " ≫ "
         (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `colimit.ι [`diagram (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `colim.map [(Term.hole "_")])
        " ≫ "
        (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `colim.map [(Term.hole "_")])
       " ≫ "
       (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colimit.iso_colimit_cocone
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `colim.map [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colim.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `colimit.ι [`diagram (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `diagram
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colimit.ι
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `colimit.ι [`diagram (Term.hole "_")])
      " ≫ "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `colim.map [(Term.hole "_")])
       " ≫ "
       (Term.proj
        (Term.paren "(" (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) ")")
        "."
        `Hom)))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `colimit.ι [`diagram (Term.hole "_")])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `colim.map [(Term.hole "_")])
         " ≫ "
         (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `colimit.ι [`diagram (Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `colim.map [(Term.hole "_")])
        " ≫ "
        (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `colim.map [(Term.hole "_")])
       " ≫ "
       (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colimit.iso_colimit_cocone
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `colim.map [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colim.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `colimit.ι [`diagram (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `diagram
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colimit.ι
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `colimit.ι [`diagram (Term.hole "_")])
      " ≫ "
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `colim.map [(Term.hole "_")])
       " ≫ "
       (Term.proj
        (Term.paren "(" (Term.app `colimit.iso_colimit_cocone [(Term.hole "_")]) ")")
        "."
        `Hom)))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app `colimit.ι [`diagram `one `x])
            "="
            (Term.app `colimit.ι [`diagram `one `y])))]
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ι_preserves_colimits_iso_hom)]
               "]")
              [])
             []
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])]))))))
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ι_preserves_colimits_iso_hom)]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `ι_preserves_colimits_iso_hom)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ι_preserves_colimits_iso_hom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `colimit.ι [`diagram `one `x])
       "="
       (Term.app `colimit.ι [`diagram `one `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `colimit.ι [`diagram `one `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `diagram
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colimit.ι
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `colimit.ι [`diagram `one `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `diagram
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `colimit.ι
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `diagram
         []
         []
         ":="
         (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          (Term.app
           `parallel_pair
           [(Term.proj
             (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
             "."
             `fstSigmaMap)
            (Term.proj
             (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
             "."
             `sndSigmaMap)])
          " ⋙ "
          (Term.app `forget [(Term.hole "_")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (Term.app
        `parallel_pair
        [(Term.proj
          (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
          "."
          `fstSigmaMap)
         (Term.proj
          (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
          "."
          `sndSigmaMap)])
       " ⋙ "
       (Term.app `forget [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `forget [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       `parallel_pair
       [(Term.proj
         (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
         "."
         `fstSigmaMap)
        (Term.proj
         (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
         "."
         `sndSigmaMap)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
       "."
       `sndSigmaMap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `diagram)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
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
  eqv_gen_of_π_eq
  { x y : ∐ D . U } ( h : 𝖣 . π x = 𝖣 . π y )
    : EqvGen Types.CoequalizerRel 𝖣 . diagram . fstSigmaMap 𝖣 . diagram . sndSigmaMap x y
  :=
    by
      delta glue_data.π multicoequalizer.sigma_π at h
        simp_rw [ comp_app ] at h
        replace
          h := TopCat.mono_iff_injective multicoequalizer.iso_coequalizer 𝖣 . diagram . inv . mp _ h
        let diagram := parallel_pair 𝖣 . diagram . fstSigmaMap 𝖣 . diagram . sndSigmaMap ⋙ forget _
        have
          : colimit.ι diagram one x = colimit.ι diagram one y
            :=
            by rw [ ← ι_preserves_colimits_iso_hom ] simp [ h ]
        have
          :
              colimit.ι diagram _ ≫ colim.map _ ≫ colimit.iso_colimit_cocone _ . Hom _
                =
                colimit.ι diagram _ ≫ colim.map _ ≫ colimit.iso_colimit_cocone _ . Hom _
            :=
            (
              congr_arg
                colim.map diagram_iso_parallel_pair diagram . Hom
                    ≫
                    colimit.iso_colimit_cocone types.coequalizer_colimit _ _ . Hom
                  this
              :
              _
              )
        simp
          only
          [
            eq_to_hom_refl
              ,
              types_comp_apply
              ,
              colimit.ι_map_assoc
              ,
              diagram_iso_parallel_pair_hom_app
              ,
              colimit.iso_colimit_cocone_ι_hom
              ,
              types_id_apply
            ]
          at this
        exact Quot.eq . 1 this
        infer_instance
#align Top.glue_data.eqv_gen_of_π_eq TopCat.GlueData.eqv_gen_of_π_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_eq_iff_rel [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder "(" [`x] [":" (Term.app (Term.proj `D "." `U) [`i])] [] ")")
        (Term.explicitBinder "(" [`y] [":" (Term.app (Term.proj `D "." `U) [`j])] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i `x])
          "="
          (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j `y]))
         "↔"
         (Term.app
          (Term.proj `D "." `Rel)
          [(Term.anonymousCtor "⟨" [`i "," `x] "⟩") (Term.anonymousCtor "⟨" [`j "," `y] "⟩")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.delta "delta" [`glue_data.ι] [])
             []
             (Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multicoequalizer.ι_sigma_π)]
               "]")
              [])
             []
             (Tactic.intro "intro" [`h])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.show
                  "show"
                  («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`i `x]))
                  (Term.fromTerm
                   "from"
                   (Term.app
                    `concrete_category.congr_hom
                    [(Term.proj
                      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
                      "."
                      `inv_hom_id)
                     (Term.hole "_")]))))]
               "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.show
                  "show"
                  («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`j `y]))
                  (Term.fromTerm
                   "from"
                   (Term.app
                    `concrete_category.congr_hom
                    [(Term.proj
                      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
                      "."
                      `inv_hom_id)
                     (Term.hole "_")]))))]
               "]")
              [])
             []
             (Tactic.change
              "change"
              (Term.app
               `InvImage
               [`D.rel
                (Term.proj
                 (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
                 "."
                 `Hom)
                (Term.hole "_")
                (Term.hole "_")])
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `TopCat.sigma_iso_sigma_inv_apply)] "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.proj
                  (Term.app `InvImage.equivalence [(Term.hole "_") (Term.hole "_") `D.rel_equiv])
                  "."
                  `eqv_gen_iff))]
               "]")
              [])
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `EqvGen.mono
               [(Term.hole "_")
                (Term.typeAscription
                 "("
                 (Term.app `D.eqv_gen_of_π_eq [`h])
                 ":"
                 [(Term.hole "_")]
                 ")")]))
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.show
                  "show"
                  («term_=_»
                   (Term.app
                    (Term.proj
                     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
                     "."
                     `inv)
                    [(Term.hole "_")])
                   "="
                   `x)
                  (Term.fromTerm
                   "from"
                   (Term.app
                    `concrete_category.congr_hom
                    [(Term.proj
                      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
                      "."
                      `hom_inv_id)
                     `x]))))]
               "]")
              [])
             []
             (Tactic.generalize
              "generalize"
              [(Tactic.generalizeArg
                []
                (Term.app
                 (Term.proj
                  (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.V])
                  "."
                  `Hom)
                 [`x])
                "="
                `x')]
              [])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                    [])]
                  "⟩")])]
              []
              [":=" [`x']])
             []
             (Tactic.unfold
              "unfold"
              [`InvImage `multispan_index.fst_sigma_map `multispan_index.snd_sigma_map]
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `opens.inclusion_apply)
                ","
                (Tactic.simpLemma [] [] `TopCat.comp_app)
                ","
                (Tactic.simpLemma [] [] `sigma_iso_sigma_inv_apply)
                ","
                (Tactic.simpLemma [] [] `CategoryTheory.Limits.colimit.ι_desc_apply)
                ","
                (Tactic.simpLemma [] [] `cofan.mk_ι_app)
                ","
                (Tactic.simpLemma [] [] `sigma_iso_sigma_hom_ι_apply)
                ","
                (Tactic.simpLemma [] [] `ContinuousMap.to_fun_eq_coe)]
               "]"]
              [])
             []
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `sigma_iso_sigma_hom_ι_apply)
                ","
                (Tactic.rwRule [] `sigma_iso_sigma_hom_ι_apply)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `Or.inr
               [(Term.anonymousCtor
                 "⟨"
                 [`y
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.dsimp
                       "dsimp"
                       []
                       []
                       []
                       ["[" [(Tactic.simpLemma [] [] `glue_data.diagram)] "]"]
                       [])
                      []
                      (Tactic.simp "simp" [] [] [] [] [])])))]
                 "⟩")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                       [])]
                     "⟩")])
                  [])
                 ")"))]
              [])
             []
             (Tactic.tacticRfl "rfl")
             []
             (Tactic.dsimp
              "dsimp"
              []
              []
              ["only"]
              []
              [(Tactic.location "at" (Tactic.locationWildcard "*"))])
             []
             (Tactic.subst "subst" [`e₁])
             []
             (Tactic.subst "subst" [`e₂])
             []
             (Tactic.simp "simp" [] [] [] [] [])])])))
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
         [(Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.delta "delta" [`glue_data.ι] [])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multicoequalizer.ι_sigma_π)]
              "]")
             [])
            []
            (Tactic.intro "intro" [`h])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.show
                 "show"
                 («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`i `x]))
                 (Term.fromTerm
                  "from"
                  (Term.app
                   `concrete_category.congr_hom
                   [(Term.proj
                     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
                     "."
                     `inv_hom_id)
                    (Term.hole "_")]))))]
              "]")
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.show
                 "show"
                 («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`j `y]))
                 (Term.fromTerm
                  "from"
                  (Term.app
                   `concrete_category.congr_hom
                   [(Term.proj
                     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
                     "."
                     `inv_hom_id)
                    (Term.hole "_")]))))]
              "]")
             [])
            []
            (Tactic.change
             "change"
             (Term.app
              `InvImage
              [`D.rel
               (Term.proj
                (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
                "."
                `Hom)
               (Term.hole "_")
               (Term.hole "_")])
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `TopCat.sigma_iso_sigma_inv_apply)] "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.proj
                 (Term.app `InvImage.equivalence [(Term.hole "_") (Term.hole "_") `D.rel_equiv])
                 "."
                 `eqv_gen_iff))]
              "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `EqvGen.mono
              [(Term.hole "_")
               (Term.typeAscription
                "("
                (Term.app `D.eqv_gen_of_π_eq [`h])
                ":"
                [(Term.hole "_")]
                ")")]))
            []
            (Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.show
                 "show"
                 («term_=_»
                  (Term.app
                   (Term.proj
                    (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
                    "."
                    `inv)
                   [(Term.hole "_")])
                  "="
                  `x)
                 (Term.fromTerm
                  "from"
                  (Term.app
                   `concrete_category.congr_hom
                   [(Term.proj
                     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
                     "."
                     `hom_inv_id)
                    `x]))))]
              "]")
             [])
            []
            (Tactic.generalize
             "generalize"
             [(Tactic.generalizeArg
               []
               (Term.app
                (Term.proj
                 (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.V])
                 "."
                 `Hom)
                [`x])
               "="
               `x')]
             [])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                        [])]
                      "⟩")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                   [])]
                 "⟩")])]
             []
             [":=" [`x']])
            []
            (Tactic.unfold
             "unfold"
             [`InvImage `multispan_index.fst_sigma_map `multispan_index.snd_sigma_map]
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `opens.inclusion_apply)
               ","
               (Tactic.simpLemma [] [] `TopCat.comp_app)
               ","
               (Tactic.simpLemma [] [] `sigma_iso_sigma_inv_apply)
               ","
               (Tactic.simpLemma [] [] `CategoryTheory.Limits.colimit.ι_desc_apply)
               ","
               (Tactic.simpLemma [] [] `cofan.mk_ι_app)
               ","
               (Tactic.simpLemma [] [] `sigma_iso_sigma_hom_ι_apply)
               ","
               (Tactic.simpLemma [] [] `ContinuousMap.to_fun_eq_coe)]
              "]"]
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `sigma_iso_sigma_hom_ι_apply)
               ","
               (Tactic.rwRule [] `sigma_iso_sigma_hom_ι_apply)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `Or.inr
              [(Term.anonymousCtor
                "⟨"
                [`y
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.dsimp
                      "dsimp"
                      []
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [] `glue_data.diagram)] "]"]
                      [])
                     []
                     (Tactic.simp "simp" [] [] [] [] [])])))]
                "⟩")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                      [])]
                    "⟩")])
                 [])
                ")"))]
             [])
            []
            (Tactic.tacticRfl "rfl")
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             ["only"]
             []
             [(Tactic.location "at" (Tactic.locationWildcard "*"))])
            []
            (Tactic.subst "subst" [`e₁])
            []
            (Tactic.subst "subst" [`e₂])
            []
            (Tactic.simp "simp" [] [] [] [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                  [])]
                "⟩")
               "|"
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                  [])]
                "⟩")])
             [])
            ")"))]
         [])
        []
        (Tactic.tacticRfl "rfl")
        []
        (Tactic.dsimp
         "dsimp"
         []
         []
         ["only"]
         []
         [(Tactic.location "at" (Tactic.locationWildcard "*"))])
        []
        (Tactic.subst "subst" [`e₁])
        []
        (Tactic.subst "subst" [`e₂])
        []
        (Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`e₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.subst "subst" [`e₁])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       []
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.paren
          "("
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                [])]
              "⟩")
             "|"
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                [])]
              "⟩")])
           [])
          ")"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.delta "delta" [`glue_data.ι] [])
        []
        (Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multicoequalizer.ι_sigma_π)]
          "]")
         [])
        []
        (Tactic.intro "intro" [`h])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.show
             "show"
             («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`i `x]))
             (Term.fromTerm
              "from"
              (Term.app
               `concrete_category.congr_hom
               [(Term.proj
                 (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
                 "."
                 `inv_hom_id)
                (Term.hole "_")]))))]
          "]")
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.show
             "show"
             («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`j `y]))
             (Term.fromTerm
              "from"
              (Term.app
               `concrete_category.congr_hom
               [(Term.proj
                 (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
                 "."
                 `inv_hom_id)
                (Term.hole "_")]))))]
          "]")
         [])
        []
        (Tactic.change
         "change"
         (Term.app
          `InvImage
          [`D.rel
           (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U]) "." `Hom)
           (Term.hole "_")
           (Term.hole "_")])
         [])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `TopCat.sigma_iso_sigma_inv_apply)] "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.proj
             (Term.app `InvImage.equivalence [(Term.hole "_") (Term.hole "_") `D.rel_equiv])
             "."
             `eqv_gen_iff))]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `EqvGen.mono
          [(Term.hole "_")
           (Term.typeAscription "(" (Term.app `D.eqv_gen_of_π_eq [`h]) ":" [(Term.hole "_")] ")")]))
        []
        (Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
          (Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.show
             "show"
             («term_=_»
              (Term.app
               (Term.proj
                (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
                "."
                `inv)
               [(Term.hole "_")])
              "="
              `x)
             (Term.fromTerm
              "from"
              (Term.app
               `concrete_category.congr_hom
               [(Term.proj
                 (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
                 "."
                 `hom_inv_id)
                `x]))))]
          "]")
         [])
        []
        (Tactic.generalize
         "generalize"
         [(Tactic.generalizeArg
           []
           (Term.app
            (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.V]) "." `Hom)
            [`x])
           "="
           `x')]
         [])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                    [])]
                  "⟩")])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
               [])]
             "⟩")])]
         []
         [":=" [`x']])
        []
        (Tactic.unfold
         "unfold"
         [`InvImage `multispan_index.fst_sigma_map `multispan_index.snd_sigma_map]
         [])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `opens.inclusion_apply)
           ","
           (Tactic.simpLemma [] [] `TopCat.comp_app)
           ","
           (Tactic.simpLemma [] [] `sigma_iso_sigma_inv_apply)
           ","
           (Tactic.simpLemma [] [] `CategoryTheory.Limits.colimit.ι_desc_apply)
           ","
           (Tactic.simpLemma [] [] `cofan.mk_ι_app)
           ","
           (Tactic.simpLemma [] [] `sigma_iso_sigma_hom_ι_apply)
           ","
           (Tactic.simpLemma [] [] `ContinuousMap.to_fun_eq_coe)]
          "]"]
         [])
        []
        (Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `sigma_iso_sigma_hom_ι_apply)
           ","
           (Tactic.rwRule [] `sigma_iso_sigma_hom_ι_apply)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `Or.inr
          [(Term.anonymousCtor
            "⟨"
            [`y
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.dsimp
                  "dsimp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [] `glue_data.diagram)] "]"]
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Or.inr
        [(Term.anonymousCtor
          "⟨"
          [`y
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.dsimp
                "dsimp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] `glue_data.diagram)] "]"]
                [])
               []
               (Tactic.simp "simp" [] [] [] [] [])])))]
          "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Or.inr
       [(Term.anonymousCtor
         "⟨"
         [`y
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.dsimp
               "dsimp"
               []
               []
               []
               ["[" [(Tactic.simpLemma [] [] `glue_data.diagram)] "]"]
               [])
              []
              (Tactic.simp "simp" [] [] [] [] [])])))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`y
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.dsimp
             "dsimp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `glue_data.diagram)] "]"]
             [])
            []
            (Tactic.simp "simp" [] [] [] [] [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `glue_data.diagram)] "]"] [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `glue_data.diagram)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `glue_data.diagram
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `sigma_iso_sigma_hom_ι_apply)
         ","
         (Tactic.rwRule [] `sigma_iso_sigma_hom_ι_apply)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sigma_iso_sigma_hom_ι_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sigma_iso_sigma_hom_ι_apply
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
        [(Tactic.simpLemma [] [] `opens.inclusion_apply)
         ","
         (Tactic.simpLemma [] [] `TopCat.comp_app)
         ","
         (Tactic.simpLemma [] [] `sigma_iso_sigma_inv_apply)
         ","
         (Tactic.simpLemma [] [] `CategoryTheory.Limits.colimit.ι_desc_apply)
         ","
         (Tactic.simpLemma [] [] `cofan.mk_ι_app)
         ","
         (Tactic.simpLemma [] [] `sigma_iso_sigma_hom_ι_apply)
         ","
         (Tactic.simpLemma [] [] `ContinuousMap.to_fun_eq_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ContinuousMap.to_fun_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sigma_iso_sigma_hom_ι_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cofan.mk_ι_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `CategoryTheory.Limits.colimit.ι_desc_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sigma_iso_sigma_inv_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat.comp_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `opens.inclusion_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.unfold
       "unfold"
       [`InvImage `multispan_index.fst_sigma_map `multispan_index.snd_sigma_map]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                  [])]
                "⟩")])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
             [])]
           "⟩")])]
       []
       [":=" [`x']])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.generalize
       "generalize"
       [(Tactic.generalizeArg
         []
         (Term.app
          (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.V]) "." `Hom)
          [`x])
         "="
         `x')]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.V]) "." `Hom)
       [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.V]) "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.V])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.V
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sigmaIsoSigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.V])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.show
           "show"
           («term_=_»
            (Term.app
             (Term.proj
              (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
              "."
              `inv)
             [(Term.hole "_")])
            "="
            `x)
           (Term.fromTerm
            "from"
            (Term.app
             `concrete_category.congr_hom
             [(Term.proj
               (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
               "."
               `hom_inv_id)
              `x]))))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app
         (Term.proj
          (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
          "."
          `inv)
         [(Term.hole "_")])
        "="
        `x)
       (Term.fromTerm
        "from"
        (Term.app
         `concrete_category.congr_hom
         [(Term.proj
           (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
           "."
           `hom_inv_id)
          `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `concrete_category.congr_hom
       [(Term.proj
         (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
         "."
         `hom_inv_id)
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
       "."
       `hom_inv_id)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sigmaIsoSigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `concrete_category.congr_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj
         (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
         "."
         `inv)
        [(Term.hole "_")])
       "="
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (Term.proj
        (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
        "."
        `inv)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
       "."
       `inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sigmaIsoSigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `EqvGen.mono
        [(Term.hole "_")
         (Term.typeAscription "(" (Term.app `D.eqv_gen_of_π_eq [`h]) ":" [(Term.hole "_")] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `EqvGen.mono
       [(Term.hole "_")
        (Term.typeAscription "(" (Term.app `D.eqv_gen_of_π_eq [`h]) ":" [(Term.hole "_")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (Term.app `D.eqv_gen_of_π_eq [`h]) ":" [(Term.hole "_")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.eqv_gen_of_π_eq [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.eqv_gen_of_π_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `EqvGen.mono
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
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (Term.app `InvImage.equivalence [(Term.hole "_") (Term.hole "_") `D.rel_equiv])
           "."
           `eqv_gen_iff))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `InvImage.equivalence [(Term.hole "_") (Term.hole "_") `D.rel_equiv])
       "."
       `eqv_gen_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `InvImage.equivalence [(Term.hole "_") (Term.hole "_") `D.rel_equiv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.rel_equiv
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `InvImage.equivalence
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `InvImage.equivalence [(Term.hole "_") (Term.hole "_") `D.rel_equiv])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `TopCat.sigma_iso_sigma_inv_apply)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat.sigma_iso_sigma_inv_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.app
        `InvImage
        [`D.rel
         (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U]) "." `Hom)
         (Term.hole "_")
         (Term.hole "_")])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `InvImage
       [`D.rel
        (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U]) "." `Hom)
        (Term.hole "_")
        (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U]) "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sigmaIsoSigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D.rel
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `InvImage
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
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.show
           "show"
           («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`j `y]))
           (Term.fromTerm
            "from"
            (Term.app
             `concrete_category.congr_hom
             [(Term.proj
               (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
               "."
               `inv_hom_id)
              (Term.hole "_")]))))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`j `y]))
       (Term.fromTerm
        "from"
        (Term.app
         `concrete_category.congr_hom
         [(Term.proj
           (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
           "."
           `inv_hom_id)
          (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `concrete_category.congr_hom
       [(Term.proj
         (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
         "."
         `inv_hom_id)
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U]) "." `inv_hom_id)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sigmaIsoSigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `concrete_category.congr_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`j `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Sigma.mk [`j `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Sigma.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.show
           "show"
           («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`i `x]))
           (Term.fromTerm
            "from"
            (Term.app
             `concrete_category.congr_hom
             [(Term.proj
               (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
               "."
               `inv_hom_id)
              (Term.hole "_")]))))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`i `x]))
       (Term.fromTerm
        "from"
        (Term.app
         `concrete_category.congr_hom
         [(Term.proj
           (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
           "."
           `inv_hom_id)
          (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `concrete_category.congr_hom
       [(Term.proj
         (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
         "."
         `inv_hom_id)
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.proj (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U]) "." `inv_hom_id)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sigmaIsoSigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicitUniv `sigmaIsoSigma ".{" [`u] "}") [`D.U])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `concrete_category.congr_hom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.app `Sigma.mk [`i `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Sigma.mk [`i `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Sigma.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `multicoequalizer.ι_sigma_π)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `multicoequalizer.ι_sigma_π
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.delta "delta" [`glue_data.ι] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_»
        (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i `x])
        "="
        (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j `y]))
       "↔"
       (Term.app
        (Term.proj `D "." `Rel)
        [(Term.anonymousCtor "⟨" [`i "," `x] "⟩") (Term.anonymousCtor "⟨" [`j "," `y] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `D "." `Rel)
       [(Term.anonymousCtor "⟨" [`i "," `x] "⟩") (Term.anonymousCtor "⟨" [`j "," `y] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`j "," `y] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.anonymousCtor "⟨" [`i "," `x] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `Rel)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_»
       (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i `x])
       "="
       (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ι_eq_iff_rel
  ( i j : D . J ) ( x : D . U i ) ( y : D . U j )
    : 𝖣 . ι i x = 𝖣 . ι j y ↔ D . Rel ⟨ i , x ⟩ ⟨ j , y ⟩
  :=
    by
      constructor
        ·
          delta glue_data.ι
            simp_rw [ ← multicoequalizer.ι_sigma_π ]
            intro h
            rw
              [
                ←
                  show
                    _ = Sigma.mk i x
                    from concrete_category.congr_hom sigmaIsoSigma .{ u } D.U . inv_hom_id _
                ]
            rw
              [
                ←
                  show
                    _ = Sigma.mk j y
                    from concrete_category.congr_hom sigmaIsoSigma .{ u } D.U . inv_hom_id _
                ]
            change InvImage D.rel sigmaIsoSigma .{ u } D.U . Hom _ _
            simp only [ TopCat.sigma_iso_sigma_inv_apply ]
            rw [ ← InvImage.equivalence _ _ D.rel_equiv . eqv_gen_iff ]
            refine' EqvGen.mono _ ( D.eqv_gen_of_π_eq h : _ )
            rintro _ _ ⟨ x ⟩
            rw
              [
                ←
                  show
                    sigmaIsoSigma .{ u } _ . inv _ = x
                    from concrete_category.congr_hom sigmaIsoSigma .{ u } _ . hom_inv_id x
                ]
            generalize sigmaIsoSigma .{ u } D.V . Hom x = x'
            obtain ⟨ ⟨ i , j ⟩ , y ⟩ := x'
            unfold InvImage multispan_index.fst_sigma_map multispan_index.snd_sigma_map
            simp
              only
              [
                opens.inclusion_apply
                  ,
                  TopCat.comp_app
                  ,
                  sigma_iso_sigma_inv_apply
                  ,
                  CategoryTheory.Limits.colimit.ι_desc_apply
                  ,
                  cofan.mk_ι_app
                  ,
                  sigma_iso_sigma_hom_ι_apply
                  ,
                  ContinuousMap.to_fun_eq_coe
                ]
            erw [ sigma_iso_sigma_hom_ι_apply , sigma_iso_sigma_hom_ι_apply ]
            exact Or.inr ⟨ y , by dsimp [ glue_data.diagram ] simp ⟩
        · rintro ( ⟨ ⟨ ⟩ ⟩ | ⟨ z , e₁ , e₂ ⟩ ) rfl dsimp only at * subst e₁ subst e₂ simp
#align Top.glue_data.ι_eq_iff_rel TopCat.GlueData.ι_eq_iff_rel

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_injective [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Function.Injective
         [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [`x `y `h])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              (Term.app
               (Term.proj
                (Term.app
                 `D.ι_eq_iff_rel
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
                "."
                `mp)
               [`h]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                       [])]
                     "⟩")])
                  [])
                 ")")])
              [])])
           []
           (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.tacticRfl "rfl")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.dsimp
              "dsimp"
              []
              []
              ["only"]
              []
              [(Tactic.location "at" (Tactic.locationWildcard "*"))])
             []
             (Tactic.cases "cases" [(Tactic.casesTarget [] `e₁)] [] [])
             []
             (Tactic.cases "cases" [(Tactic.casesTarget [] `e₂)] [] [])
             []
             (Tactic.simp "simp" [] [] [] [] [])])])))
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
         [(Tactic.intro "intro" [`x `y `h])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              (Term.proj
               (Term.app
                `D.ι_eq_iff_rel
                [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
               "."
               `mp)
              [`h]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                      [])]
                    "⟩")])
                 [])
                ")")])
             [])])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.tacticRfl "rfl")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.dsimp
             "dsimp"
             []
             []
             ["only"]
             []
             [(Tactic.location "at" (Tactic.locationWildcard "*"))])
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `e₁)] [] [])
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `e₂)] [] [])
            []
            (Tactic.simp "simp" [] [] [] [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.dsimp
         "dsimp"
         []
         []
         ["only"]
         []
         [(Tactic.location "at" (Tactic.locationWildcard "*"))])
        []
        (Tactic.cases "cases" [(Tactic.casesTarget [] `e₁)] [] [])
        []
        (Tactic.cases "cases" [(Tactic.casesTarget [] `e₂)] [] [])
        []
        (Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `e₂)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `e₁)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       []
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj
           (Term.app
            `D.ι_eq_iff_rel
            [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
           "."
           `mp)
          [`h]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                  [])]
                "⟩")
               "|"
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                  [])]
                "⟩")])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `D.ι_eq_iff_rel [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `mp)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `D.ι_eq_iff_rel [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.ι_eq_iff_rel [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.ι_eq_iff_rel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.ι_eq_iff_rel [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `y `h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Function.Injective
       [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ι_injective
  ( i : D . J ) : Function.Injective 𝖣 . ι i
  :=
    by
      intro x y h
        rcases D.ι_eq_iff_rel _ _ _ _ . mp h with ( ⟨ ⟨ ⟩ ⟩ | ⟨ _ , e₁ , e₂ ⟩ )
        · rfl
        · dsimp only at * cases e₁ cases e₂ simp
#align Top.glue_data.ι_injective TopCat.GlueData.ι_injective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `ι_mono [])]
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Mono
         [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.app `TopCat.mono_iff_injective [(Term.hole "_")]) "." `mpr)
        [(Term.app (Term.proj `D "." `ι_injective) [(Term.hole "_")])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `TopCat.mono_iff_injective [(Term.hole "_")]) "." `mpr)
       [(Term.app (Term.proj `D "." `ι_injective) [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `D "." `ι_injective) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `ι_injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `ι_injective) [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `TopCat.mono_iff_injective [(Term.hole "_")]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `TopCat.mono_iff_injective [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TopCat.mono_iff_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `TopCat.mono_iff_injective [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Mono
       [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance ι_mono ( i : D . J ) : Mono 𝖣 . ι i := TopCat.mono_iff_injective _ . mpr D . ι_injective _
#align Top.glue_data.ι_mono TopCat.GlueData.ι_mono

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `image_inter [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_∩_»
          (Term.app
           `Set.range
           [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])])
          "∩"
          (Term.app
           `Set.range
           [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])]))
         "="
         (Term.app
          `Set.range
          [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app (Term.proj `D "." `f) [`i `j])
            " ≫ "
            (Term.app
             (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
             [(Term.hole "_")]))]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
            [])
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq₁)])
                        [])]
                      "⟩")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₂)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq₂)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩"))]
              [])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                    [])]
                  "⟩")
                 "|"
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                    [])]
                  "⟩")])]
              []
              [":="
               [(Term.app
                 (Term.proj
                  (Term.app
                   `D.ι_eq_iff_rel
                   [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
                  "."
                  `mp)
                 [(Term.app `eq₁.trans [`eq₂.symm])])]])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `inv [(Term.app `D.f [`i `i]) `x₁])
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["[" [(Tactic.simpLemma [] [] `eq₁)] "]"]
                       [])])))]
                 "⟩"))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.dsimp
                "dsimp"
                []
                []
                ["only"]
                []
                [(Tactic.location "at" (Tactic.locationWildcard "*"))])
               []
               (Mathlib.Tactic.Substs.substs "substs" [`e₁ `eq₁])
               []
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [`y
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
                 "⟩"))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor "⟨" [(Term.app `D.f [`i `j `x]) "," `hx] "⟩")
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `D.f [`j `i (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])])
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       []
                       ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx)] "]"]
                       [])])))]
                 "⟩")]
               "⟩"))])])))
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
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
           [])
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq₁)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₂)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq₂)])
                       [])]
                     "⟩")])
                  [])]
                "⟩"))]
             [])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
                   [])]
                 "⟩")
                "|"
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
                   [])]
                 "⟩")])]
             []
             [":="
              [(Term.app
                (Term.proj
                 (Term.app
                  `D.ι_eq_iff_rel
                  [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
                 "."
                 `mp)
                [(Term.app `eq₁.trans [`eq₂.symm])])]])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `inv [(Term.app `D.f [`i `i]) `x₁])
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq₁)] "]"] [])])))]
                "⟩"))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.dsimp
               "dsimp"
               []
               []
               ["only"]
               []
               [(Tactic.location "at" (Tactic.locationWildcard "*"))])
              []
              (Mathlib.Tactic.Substs.substs "substs" [`e₁ `eq₁])
              []
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`y
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
                "⟩"))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor "⟨" [(Term.app `D.f [`i `j `x]) "," `hx] "⟩")
               ","
               (Term.anonymousCtor
                "⟨"
                [(Term.app `D.f [`j `i (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])])
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx)] "]"]
                      [])])))]
                "⟩")]
              "⟩"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor "⟨" [(Term.app `D.f [`i `j `x]) "," `hx] "⟩")
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.app `D.f [`j `i (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])])
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx)] "]"]
                  [])])))]
            "⟩")]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor "⟨" [(Term.app `D.f [`i `j `x]) "," `hx] "⟩")
         ","
         (Term.anonymousCtor
          "⟨"
          [(Term.app `D.f [`j `i (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])])
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx)] "]"]
                [])])))]
          "⟩")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [(Term.app `D.f [`i `j `x]) "," `hx] "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.app `D.f [`j `i (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])])
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx)] "]"]
               [])])))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `D.f [`j `i (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx)] "]"]
             [])])))]
       "⟩")
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
           ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hx)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.f [`j `i (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.t [(Term.hole "_") (Term.hole "_") `x])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `D.f [`i `j `x]) "," `hx] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.f [`i `j `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq₁)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₂)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq₂)])
                   [])]
                 "⟩")])
              [])]
            "⟩"))]
         [])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
               [])]
             "⟩")
            "|"
            (Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
               [])]
             "⟩")])]
         []
         [":="
          [(Term.app
            (Term.proj
             (Term.app
              `D.ι_eq_iff_rel
              [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
             "."
             `mp)
            [(Term.app `eq₁.trans [`eq₂.symm])])]])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.app `inv [(Term.app `D.f [`i `i]) `x₁])
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq₁)] "]"] [])])))]
            "⟩"))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           []
           [(Tactic.location "at" (Tactic.locationWildcard "*"))])
          []
          (Mathlib.Tactic.Substs.substs "substs" [`e₁ `eq₁])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [`y
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩"))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.dsimp
         "dsimp"
         []
         []
         ["only"]
         []
         [(Tactic.location "at" (Tactic.locationWildcard "*"))])
        []
        (Mathlib.Tactic.Substs.substs "substs" [`e₁ `eq₁])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`y
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`y
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`y
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Substs.substs "substs" [`e₁ `eq₁])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       []
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `inv [(Term.app `D.f [`i `i]) `x₁])
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq₁)] "]"] [])])))]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `inv [(Term.app `D.f [`i `i]) `x₁])
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq₁)] "]"] [])])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `inv [(Term.app `D.f [`i `i]) `x₁])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq₁)] "]"] [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq₁)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq₁)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv [(Term.app `D.f [`i `i]) `x₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.f [`i `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `D.f [`i `i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.tuple "⟨" [] "⟩")])
             [])]
           "⟩")
          "|"
          (Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₁)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `e₂)])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          (Term.proj
           (Term.app
            `D.ι_eq_iff_rel
            [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
           "."
           `mp)
          [(Term.app `eq₁.trans [`eq₂.symm])])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `D.ι_eq_iff_rel [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `mp)
       [(Term.app `eq₁.trans [`eq₂.symm])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq₁.trans [`eq₂.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq₂.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq₁.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `eq₁.trans [`eq₂.symm]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `D.ι_eq_iff_rel [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.ι_eq_iff_rel [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.ι_eq_iff_rel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.ι_eq_iff_rel [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq₁)])
                 [])]
               "⟩")])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₂)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq₂)])
                 [])]
               "⟩")])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_∩_»
        (Term.app
         `Set.range
         [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])])
        "∩"
        (Term.app
         `Set.range
         [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])]))
       "="
       (Term.app
        `Set.range
        [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (Term.proj `D "." `f) [`i `j])
          " ≫ "
          (Term.app
           (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
           [(Term.hole "_")]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.range
       [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app (Term.proj `D "." `f) [`i `j])
         " ≫ "
         (Term.app
          (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
          [(Term.hole "_")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app (Term.proj `D "." `f) [`i `j])
       " ≫ "
       (Term.app
        (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  image_inter
  ( i j : D . J ) : Set.range 𝖣 . ι i ∩ Set.range 𝖣 . ι j = Set.range D . f i j ≫ 𝖣 . ι _
  :=
    by
      ext x
        constructor
        ·
          rintro ⟨ ⟨ x₁ , eq₁ ⟩ , ⟨ x₂ , eq₂ ⟩ ⟩
            obtain ⟨ ⟨ ⟩ ⟩ | ⟨ y , e₁ , e₂ ⟩ := D.ι_eq_iff_rel _ _ _ _ . mp eq₁.trans eq₂.symm
            · exact ⟨ inv D.f i i x₁ , by simp [ eq₁ ] ⟩
            · dsimp only at * substs e₁ eq₁ exact ⟨ y , by simp ⟩
        · rintro ⟨ x , hx ⟩ exact ⟨ ⟨ D.f i j x , hx ⟩ , ⟨ D.f j i D.t _ _ x , by simp [ ← hx ] ⟩ ⟩
#align Top.glue_data.image_inter TopCat.GlueData.image_inter

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `preimage_range [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.«term_⁻¹'_»
          (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])
          " ⁻¹' "
          (Term.app
           `Set.range
           [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])]))
         "="
         (Term.app `Set.range [(Term.app (Term.proj `D "." `f) [`j `i])]))))
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
               (Term.app
                `Set.preimage_image_eq
                [(Term.app `Set.range [(Term.app `D.f [`j `i])]) (Term.app `D.ι_injective [`j])]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_comp)
              ","
              (Tactic.rwRule [] `Set.image_univ)
              ","
              (Tactic.rwRule [] `Set.image_univ)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_inter)
              ","
              (Tactic.rwRule [] `Set.preimage_range_inter)]
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `Set.preimage_image_eq
               [(Term.app `Set.range [(Term.app `D.f [`j `i])]) (Term.app `D.ι_injective [`j])]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_comp)
             ","
             (Tactic.rwRule [] `Set.image_univ)
             ","
             (Tactic.rwRule [] `Set.image_univ)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_inter)
             ","
             (Tactic.rwRule [] `Set.preimage_range_inter)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `Set.preimage_image_eq
           [(Term.app `Set.range [(Term.app `D.f [`j `i])]) (Term.app `D.ι_injective [`j])]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_comp)
         ","
         (Tactic.rwRule [] `Set.image_univ)
         ","
         (Tactic.rwRule [] `Set.image_univ)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_inter)
         ","
         (Tactic.rwRule [] `Set.preimage_range_inter)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.preimage_range_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_inter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.preimage_image_eq
       [(Term.app `Set.range [(Term.app `D.f [`j `i])]) (Term.app `D.ι_injective [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.ι_injective [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.ι_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `D.ι_injective [`j]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Set.range [(Term.app `D.f [`j `i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.f [`j `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `D.f [`j `i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Set.range [(Term.paren "(" (Term.app `D.f [`j `i]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.preimage_image_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Data.Set.Image.«term_⁻¹'_»
        (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])
        " ⁻¹' "
        (Term.app
         `Set.range
         [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])]))
       "="
       (Term.app `Set.range [(Term.app (Term.proj `D "." `f) [`j `i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.range [(Term.app (Term.proj `D "." `f) [`j `i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `D "." `f) [`j `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `f) [`j `i])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.Data.Set.Image.«term_⁻¹'_»
       (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])
       " ⁻¹' "
       (Term.app
        `Set.range
        [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.range
       [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  preimage_range
  ( i j : D . J ) : 𝖣 . ι j ⁻¹' Set.range 𝖣 . ι i = Set.range D . f j i
  :=
    by
      rw
        [
          ← Set.preimage_image_eq Set.range D.f j i D.ι_injective j
            ,
            ← Set.image_univ
            ,
            ← Set.image_univ
            ,
            ← Set.image_comp
            ,
            ← coe_comp
            ,
            Set.image_univ
            ,
            Set.image_univ
            ,
            ← image_inter
            ,
            Set.preimage_range_inter
          ]
#align Top.glue_data.preimage_range TopCat.GlueData.preimage_range

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `preimage_image_eq_image [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":"
          (Term.app
           `Set
           [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `U) [`i])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.«term_⁻¹'_»
          (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])
          " ⁻¹' "
          (Set.Data.Set.Image.term_''_
           (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
           " '' "
           `U))
         "="
         (Set.Data.Set.Image.term_''_
          (Term.app (Term.proj `D "." `f) [(Term.hole "_") (Term.hole "_")])
          " '' "
          (Set.Data.Set.Image.«term_⁻¹'_»
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app (Term.proj `D "." `t) [`j `i])
            " ≫ "
            (Term.app (Term.proj `D "." `f) [(Term.hole "_") (Term.hole "_")]))
           " ⁻¹' "
           `U)))))
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
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Set.Data.Set.Image.«term_⁻¹'_»
                  (Term.app `D.f [(Term.hole "_") (Term.hole "_")])
                  " ⁻¹' "
                  (Set.Data.Set.Image.«term_⁻¹'_»
                   (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])
                   " ⁻¹' "
                   (Set.Data.Set.Image.term_''_
                    (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
                    " '' "
                    `U)))
                 "="
                 (Set.Data.Set.Image.«term_⁻¹'_»
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `D.t [`j `i])
                   " ≫ "
                   (Term.app `D.f [(Term.hole "_") (Term.hole "_")]))
                  " ⁻¹' "
                  `U)))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Ext.«tacticExt___:_»
                   "ext"
                   [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
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
                          (Term.app
                           `Set.preimage_image_eq
                           [`U (Term.app `D.ι_injective [(Term.hole "_")])]))]
                        "]"))])))
                  []
                  (Tactic.generalize
                   "generalize"
                   [(Tactic.generalizeArg
                     []
                     (Set.Data.Set.Image.term_''_
                      (Term.app
                       (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
                       [`i])
                      " '' "
                      `U)
                     "="
                     `U')]
                   [])
                  []
                  (Tactic.simp "simp" [] [] [] [] [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)
              ","
              (Tactic.rwRule [] `Set.image_preimage_eq_inter_range)]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSymm_ "symm" [])
           []
           (Tactic.apply "apply" `Set.inter_eq_self_of_subset_left)
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `D.preimage_range [`i `j]))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `Set.preimage_mono
             [(Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")])]))])))
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
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Set.Data.Set.Image.«term_⁻¹'_»
                 (Term.app `D.f [(Term.hole "_") (Term.hole "_")])
                 " ⁻¹' "
                 (Set.Data.Set.Image.«term_⁻¹'_»
                  (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])
                  " ⁻¹' "
                  (Set.Data.Set.Image.term_''_
                   (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
                   " '' "
                   `U)))
                "="
                (Set.Data.Set.Image.«term_⁻¹'_»
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `D.t [`j `i])
                  " ≫ "
                  (Term.app `D.f [(Term.hole "_") (Term.hole "_")]))
                 " ⁻¹' "
                 `U)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Ext.«tacticExt___:_»
                  "ext"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
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
                         (Term.app
                          `Set.preimage_image_eq
                          [`U (Term.app `D.ι_injective [(Term.hole "_")])]))]
                       "]"))])))
                 []
                 (Tactic.generalize
                  "generalize"
                  [(Tactic.generalizeArg
                    []
                    (Set.Data.Set.Image.term_''_
                     (Term.app
                      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
                      [`i])
                     " '' "
                     `U)
                    "="
                    `U')]
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)
             ","
             (Tactic.rwRule [] `Set.image_preimage_eq_inter_range)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSymm_ "symm" [])
          []
          (Tactic.apply "apply" `Set.inter_eq_self_of_subset_left)
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `D.preimage_range [`i `j]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `Set.preimage_mono
            [(Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `Set.preimage_mono
        [(Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.preimage_mono
       [(Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")])
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
      `Set.image_subset_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.preimage_mono
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `D.preimage_range [`i `j]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.preimage_range [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.preimage_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `Set.inter_eq_self_of_subset_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.inter_eq_self_of_subset_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSymm_ "symm" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `this)
         ","
         (Tactic.rwRule [] `Set.image_preimage_eq_inter_range)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_preimage_eq_inter_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
           («term_=_»
            (Set.Data.Set.Image.«term_⁻¹'_»
             (Term.app `D.f [(Term.hole "_") (Term.hole "_")])
             " ⁻¹' "
             (Set.Data.Set.Image.«term_⁻¹'_»
              (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])
              " ⁻¹' "
              (Set.Data.Set.Image.term_''_
               (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
               " '' "
               `U)))
            "="
            (Set.Data.Set.Image.«term_⁻¹'_»
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `D.t [`j `i])
              " ≫ "
              (Term.app `D.f [(Term.hole "_") (Term.hole "_")]))
             " ⁻¹' "
             `U)))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Ext.«tacticExt___:_»
              "ext"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
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
                     (Term.app
                      `Set.preimage_image_eq
                      [`U (Term.app `D.ι_injective [(Term.hole "_")])]))]
                   "]"))])))
             []
             (Tactic.generalize
              "generalize"
              [(Tactic.generalizeArg
                []
                (Set.Data.Set.Image.term_''_
                 (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
                 " '' "
                 `U)
                "="
                `U')]
              [])
             []
             (Tactic.simp "simp" [] [] [] [] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
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
                  (Term.app
                   `Set.preimage_image_eq
                   [`U (Term.app `D.ι_injective [(Term.hole "_")])]))]
                "]"))])))
          []
          (Tactic.generalize
           "generalize"
           [(Tactic.generalizeArg
             []
             (Set.Data.Set.Image.term_''_
              (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
              " '' "
              `U)
             "="
             `U')]
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.generalize
       "generalize"
       [(Tactic.generalizeArg
         []
         (Set.Data.Set.Image.term_''_
          (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
          " '' "
          `U)
         "="
         `U')]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
       " '' "
       `U)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
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
  preimage_image_eq_image
  ( i j : D . J ) ( U : Set 𝖣 . U i )
    : 𝖣 . ι j ⁻¹' 𝖣 . ι i '' U = D . f _ _ '' D . t j i ≫ D . f _ _ ⁻¹' U
  :=
    by
      have
          : D.f _ _ ⁻¹' 𝖣 . ι j ⁻¹' 𝖣 . ι i '' U = D.t j i ≫ D.f _ _ ⁻¹' U
            :=
            by
              ext x
                conv_rhs => rw [ ← Set.preimage_image_eq U D.ι_injective _ ]
                generalize 𝖣 . ι i '' U = U'
                simp
        rw [ ← this , Set.image_preimage_eq_inter_range ]
        symm
        apply Set.inter_eq_self_of_subset_left
        rw [ ← D.preimage_range i j ]
        exact Set.preimage_mono Set.image_subset_range _ _
#align Top.glue_data.preimage_image_eq_image TopCat.GlueData.preimage_image_eq_image

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `preimage_image_eq_image' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":"
          (Term.app
           `Set
           [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `U) [`i])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.«term_⁻¹'_»
          (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`j])
          " ⁻¹' "
          (Set.Data.Set.Image.term_''_
           (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
           " '' "
           `U))
         "="
         (Set.Data.Set.Image.term_''_
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app (Term.proj `D "." `t) [`i `j])
           " ≫ "
           (Term.app (Term.proj `D "." `f) [(Term.hole "_") (Term.hole "_")]))
          " '' "
          (Set.Data.Set.Image.«term_⁻¹'_»
           (Term.app (Term.proj `D "." `f) [(Term.hole "_") (Term.hole "_")])
           " ⁻¹' "
           `U)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(convert
            "convert"
            []
            (Term.app `D.preimage_image_eq_image [`i `j `U])
            ["using" (num "1")])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `coe_comp)
              ","
              (Tactic.rwRule [] `coe_comp)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)]
             "]")
            [])
           []
           (Tactic.congr "congr" [(num "1")])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.eq_preimage_iff_image_eq)
              ","
              (Tactic.rwRule [] `Set.preimage_preimage)]
             "]")
            [])
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.hole "_")
             "="
             (Set.Data.Set.Image.«term_⁻¹'_»
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.t [`i `j])
               " ≫ "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `D.t [`j `i])
                " ≫ "
                (Term.hole "_")))
              " ⁻¹' "
              (Term.hole "_")))
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso_iff_bijective)]
             "]")
            [])
           []
           (Tactic.apply "apply" (Term.proj (Term.app `forget [`TopCat]) "." `map_is_iso))])))
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
           (Term.app `D.preimage_image_eq_image [`i `j `U])
           ["using" (num "1")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `coe_comp)
             ","
             (Tactic.rwRule [] `coe_comp)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_image)]
            "]")
           [])
          []
          (Tactic.congr "congr" [(num "1")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.eq_preimage_iff_image_eq)
             ","
             (Tactic.rwRule [] `Set.preimage_preimage)]
            "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.hole "_")
            "="
            (Set.Data.Set.Image.«term_⁻¹'_»
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `D.t [`i `j])
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.t [`j `i])
               " ≫ "
               (Term.hole "_")))
             " ⁻¹' "
             (Term.hole "_")))
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso_iff_bijective)]
            "]")
           [])
          []
          (Tactic.apply "apply" (Term.proj (Term.app `forget [`TopCat]) "." `map_is_iso))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.proj (Term.app `forget [`TopCat]) "." `map_is_iso))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `forget [`TopCat]) "." `map_is_iso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `forget [`TopCat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `forget [`TopCat]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso_iff_bijective)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_iso_iff_bijective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `t_inv_assoc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
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
  preimage_image_eq_image'
  ( i j : D . J ) ( U : Set 𝖣 . U i )
    : 𝖣 . ι j ⁻¹' 𝖣 . ι i '' U = D . t i j ≫ D . f _ _ '' D . f _ _ ⁻¹' U
  :=
    by
      convert D.preimage_image_eq_image i j U using 1
        rw [ coe_comp , coe_comp , ← Set.image_image ]
        congr 1
        rw [ ← Set.eq_preimage_iff_image_eq , Set.preimage_preimage ]
        change _ = D.t i j ≫ D.t j i ≫ _ ⁻¹' _
        rw [ 𝖣 . t_inv_assoc ]
        rw [ ← is_iso_iff_bijective ]
        apply forget TopCat . map_is_iso
#align Top.glue_data.preimage_image_eq_image' TopCat.GlueData.preimage_image_eq_image'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `open_image_open [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":"
          (Term.app
           `Opens
           [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `U) [`i])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `IsOpen
         [(Set.Data.Set.Image.term_''_
           (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
           " '' "
           `U)])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_iff)] "]") [])
           []
           (Tactic.intro "intro" [`j])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `preimage_image_eq_image)] "]")
            [])
           []
           (Tactic.apply
            "apply"
            (Term.proj (Term.app `D.f_open [(Term.hole "_") (Term.hole "_")]) "." `IsOpenMap))
           []
           (Tactic.apply
            "apply"
            (Term.proj
             (Term.proj
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.t [`j `i])
               " ≫ "
               (Term.app `D.f [`i `j]))
              "."
              `continuous_to_fun)
             "."
             `is_open_preimage))
           []
           (Tactic.exact "exact" `U.property)])))
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_iff)] "]") [])
          []
          (Tactic.intro "intro" [`j])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `preimage_image_eq_image)] "]")
           [])
          []
          (Tactic.apply
           "apply"
           (Term.proj (Term.app `D.f_open [(Term.hole "_") (Term.hole "_")]) "." `IsOpenMap))
          []
          (Tactic.apply
           "apply"
           (Term.proj
            (Term.proj
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `D.t [`j `i])
              " ≫ "
              (Term.app `D.f [`i `j]))
             "."
             `continuous_to_fun)
            "."
            `is_open_preimage))
          []
          (Tactic.exact "exact" `U.property)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `U.property)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U.property
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj
        (Term.proj
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `D.t [`j `i])
          " ≫ "
          (Term.app `D.f [`i `j]))
         "."
         `continuous_to_fun)
        "."
        `is_open_preimage))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `D.t [`j `i])
         " ≫ "
         (Term.app `D.f [`i `j]))
        "."
        `continuous_to_fun)
       "."
       `is_open_preimage)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `D.t [`j `i])
        " ≫ "
        (Term.app `D.f [`i `j]))
       "."
       `continuous_to_fun)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `D.t [`j `i])
       " ≫ "
       (Term.app `D.f [`i `j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.f [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `D.t [`j `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.t
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.app `D.t [`j `i])
      " ≫ "
      (Term.app `D.f [`i `j]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj (Term.app `D.f_open [(Term.hole "_") (Term.hole "_")]) "." `IsOpenMap))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `D.f_open [(Term.hole "_") (Term.hole "_")]) "." `IsOpenMap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.f_open [(Term.hole "_") (Term.hole "_")])
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
      `D.f_open
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.f_open [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `preimage_image_eq_image)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `preimage_image_eq_image
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`j])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsOpen
       [(Set.Data.Set.Image.term_''_
         (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
         " '' "
         `U)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
       " '' "
       `U)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  open_image_open
  ( i : D . J ) ( U : Opens 𝖣 . U i ) : IsOpen 𝖣 . ι i '' U
  :=
    by
      rw [ is_open_iff ]
        intro j
        rw [ preimage_image_eq_image ]
        apply D.f_open _ _ . IsOpenMap
        apply D.t j i ≫ D.f i j . continuous_to_fun . is_open_preimage
        exact U.property
#align Top.glue_data.open_image_open TopCat.GlueData.open_image_open

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_open_embedding [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `OpenEmbedding
         [(Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])])))
      (Command.declValSimple
       ":="
       (Term.app
        `open_embedding_of_continuous_injective_open
        [(Term.proj
          (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
          "."
          `continuous_to_fun)
         (Term.app (Term.proj `D "." `ι_injective) [`i])
         (Term.fun
          "fun"
          (Term.basicFun
           [`U `h]
           []
           "=>"
           (Term.app
            (Term.proj `D "." `open_image_open)
            [`i (Term.anonymousCtor "⟨" [`U "," `h] "⟩")])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `open_embedding_of_continuous_injective_open
       [(Term.proj
         (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
         "."
         `continuous_to_fun)
        (Term.app (Term.proj `D "." `ι_injective) [`i])
        (Term.fun
         "fun"
         (Term.basicFun
          [`U `h]
          []
          "=>"
          (Term.app
           (Term.proj `D "." `open_image_open)
           [`i (Term.anonymousCtor "⟨" [`U "," `h] "⟩")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`U `h]
        []
        "=>"
        (Term.app
         (Term.proj `D "." `open_image_open)
         [`i (Term.anonymousCtor "⟨" [`U "," `h] "⟩")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `D "." `open_image_open) [`i (Term.anonymousCtor "⟨" [`U "," `h] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`U "," `h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `open_image_open)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app (Term.proj `D "." `ι_injective) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `ι_injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `ι_injective) [`i])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
       "."
       `continuous_to_fun)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.GlueData.Topology.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.GlueData.Topology.Gluing.«term𝖣»', expected 'TopCat.GlueData.Topology.Gluing.term𝖣._@.Topology.Gluing._hyg.20'
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
  ι_open_embedding
  ( i : D . J ) : OpenEmbedding 𝖣 . ι i
  :=
    open_embedding_of_continuous_injective_open
      𝖣 . ι i . continuous_to_fun D . ι_injective i fun U h => D . open_image_open i ⟨ U , h ⟩
#align Top.glue_data.ι_open_embedding TopCat.GlueData.ι_open_embedding

/-- A family of gluing data consists of
1. An index type `J`
2. A bundled topological space `U i` for each `i : J`.
3. An open set `V i j ⊆ U i` for each `i j : J`.
4. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `V i i = U i`.
7. `t i i` is the identity.
8. For each `x ∈ V i j ∩ V i k`, `t i j x ∈ V j k`.
9. `t j k (t i j x) = t i k x`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`.
-/
@[nolint has_nonempty_instance]
structure MkCore where
  {J : Type u}
  U : J → TopCat.{u}
  V : ∀ i, J → Opens (U i)
  t : ∀ i j, (Opens.toTop _).obj (V i j) ⟶ (Opens.toTop _).obj (V j i)
  V_id : ∀ i, V i i = ⊤
  t_id : ∀ i, ⇑(t i i) = id
  t_inter : ∀ ⦃i j⦄ (k) (x : V i j), ↑x ∈ V i k → @coe (V j i) (U j) _ (t i j x) ∈ V j k
  cocycle :
    ∀ (i j k) (x : V i j) (h : ↑x ∈ V i k),
      @coe (V k j) (U k) _ (t j k ⟨↑(t i j x), t_inter k x h⟩) = @coe (V k i) (U k) _ (t i k ⟨x, h⟩)
#align Top.glue_data.mk_core TopCat.GlueData.MkCore

theorem MkCore.t_inv (h : MkCore) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x :=
  by
  have := h.cocycle j i j x _
  rw [h.t_id] at this
  convert Subtype.eq this
  · ext
    rfl
  all_goals rw [h.V_id]; trivial
#align Top.glue_data.mk_core.t_inv TopCat.GlueData.MkCore.t_inv

instance (h : MkCore.{u}) (i j : h.J) : IsIso (h.t i j) :=
  by
  use h.t j i
  constructor <;> ext1
  exacts[h.t_inv _ _ _, h.t_inv _ _ _]

/-- (Implementation) the restricted transition map to be fed into `glue_data`. -/
def MkCore.t' (h : MkCore.{u}) (i j k : h.J) :
    pullback (h.V i j).inclusion (h.V i k).inclusion ⟶
      pullback (h.V j k).inclusion (h.V j i).inclusion :=
  by
  refine' (pullback_iso_prod_subtype _ _).Hom ≫ ⟨_, _⟩ ≫ (pullback_iso_prod_subtype _ _).inv
  · intro x
    refine' ⟨⟨⟨(h.t i j x.1.1).1, _⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
  continuity
#align Top.glue_data.mk_core.t' TopCat.GlueData.MkCore.t'

/-- This is a constructor of `Top.glue_data` whose arguments are in terms of elements and
intersections rather than subobjects and pullbacks. Please refer to `Top.glue_data.mk_core` for
details. -/
def mk' (h : MkCore.{u}) : TopCat.GlueData
    where
  J := h.J
  U := h.U
  V i := (Opens.toTop _).obj (h.V i.1 i.2)
  f i j := (h.V i j).inclusion
  f_id i := (h.V_id i).symm ▸ IsIso.of_iso (Opens.inclusionTopIso (h.U i))
  f_open := fun i j : h.J => (h.V i j).OpenEmbedding
  t := h.t
  t_id i := by
    ext
    rw [h.t_id]
    rfl
  t' := h.t'
  t_fac i j k := by
    delta mk_core.t'
    rw [category.assoc, category.assoc, pullback_iso_prod_subtype_inv_snd, ← iso.eq_inv_comp,
      pullback_iso_prod_subtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rfl
  cocycle i j k := by
    delta mk_core.t'
    simp_rw [← category.assoc]
    rw [iso.comp_inv_eq]
    simp only [iso.inv_hom_id_assoc, category.assoc, category.id_comp]
    rw [← iso.eq_inv_comp, iso.inv_hom_id]
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    simp only [TopCat.comp_app, ContinuousMap.coe_mk, Prod.mk.inj_iff, TopCat.id_app,
      Subtype.mk_eq_mk, Subtype.coe_mk]
    rw [← subtype.coe_injective.eq_iff, Subtype.val_eq_coe, Subtype.coe_mk, and_self_iff]
    convert congr_arg coe (h.t_inv k i ⟨x, hx'⟩) using 3
    ext
    exact h.cocycle i j k ⟨x, hx⟩ hx'
#align Top.glue_data.mk' TopCat.GlueData.mk'

variable {α : Type u} [TopologicalSpace α] {J : Type u} (U : J → Opens α)

include U

/-- We may construct a glue data from a family of open sets. -/
@[simps to_glue_data_J to_glue_data_U to_glue_data_V to_glue_data_t to_glue_data_f]
def ofOpenSubsets : TopCat.GlueData.{u} :=
  mk'.{u}
    { J
      U := fun i => (opens.to_Top <| TopCat.of α).obj (U i)
      V := fun i j => (opens.map <| Opens.inclusion _).obj (U j)
      t := fun i j => ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by continuity⟩
      V_id := fun i => by
        ext
        cases U i
        simp
      t_id := fun i => by
        ext
        rfl
      t_inter := fun i j k x hx => hx
      cocycle := fun i j k x h => rfl }
#align Top.glue_data.of_open_subsets TopCat.GlueData.ofOpenSubsets

/-- The canonical map from the glue of a family of open subsets `α` into `α`.
This map is an open embedding (`from_open_subsets_glue_open_embedding`),
and its range is `⋃ i, (U i : set α)` (`range_from_open_subsets_glue`).
-/
def fromOpenSubsetsGlue : (ofOpenSubsets U).toGlueData.glued ⟶ TopCat.of α :=
  multicoequalizer.desc _ _ (fun x => Opens.inclusion _)
    (by
      rintro ⟨i, j⟩
      ext x
      rfl)
#align Top.glue_data.from_open_subsets_glue TopCat.GlueData.fromOpenSubsetsGlue

@[simp, elementwise]
theorem ι_from_open_subsets_glue (i : J) :
    (ofOpenSubsets U).toGlueData.ι i ≫ fromOpenSubsetsGlue U = Opens.inclusion _ :=
  multicoequalizer.π_desc _ _ _ _ _
#align Top.glue_data.ι_from_open_subsets_glue TopCat.GlueData.ι_from_open_subsets_glue

theorem from_open_subsets_glue_injective : Function.Injective (fromOpenSubsetsGlue U) :=
  by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective y
  rw [ι_from_open_subsets_glue_apply, ι_from_open_subsets_glue_apply] at e
  change x = y at e
  subst e
  rw [(of_open_subsets U).ι_eq_iff_rel]
  right
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩
#align
  Top.glue_data.from_open_subsets_glue_injective TopCat.GlueData.from_open_subsets_glue_injective

theorem from_open_subsets_glue_is_open_map : IsOpenMap (fromOpenSubsetsGlue U) :=
  by
  intro s hs
  rw [(of_open_subsets U).is_open_iff] at hs
  rw [is_open_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x
  use from_open_subsets_glue U '' s ∩ Set.range (@opens.inclusion (TopCat.of α) (U i))
  use Set.inter_subset_left _ _
  constructor
  · erw [← Set.image_preimage_eq_inter_range]
    apply (@opens.open_embedding (TopCat.of α) (U i)).IsOpenMap
    convert hs i using 1
    rw [← ι_from_open_subsets_glue, coe_comp, Set.preimage_comp]
    congr 1
    refine' Set.preimage_image_eq _ (from_open_subsets_glue_injective U)
  · refine' ⟨Set.mem_image_of_mem _ hx, _⟩
    rw [ι_from_open_subsets_glue_apply]
    exact Set.mem_range_self _
#align
  Top.glue_data.from_open_subsets_glue_is_open_map TopCat.GlueData.from_open_subsets_glue_is_open_map

theorem from_open_subsets_glue_open_embedding : OpenEmbedding (fromOpenSubsetsGlue U) :=
  open_embedding_of_continuous_injective_open (ContinuousMap.continuous_to_fun _)
    (from_open_subsets_glue_injective U) (from_open_subsets_glue_is_open_map U)
#align
  Top.glue_data.from_open_subsets_glue_open_embedding TopCat.GlueData.from_open_subsets_glue_open_embedding

theorem range_from_open_subsets_glue : Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α) :=
  by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x
    rw [ι_from_open_subsets_glue_apply]
    exact Set.subset_unionᵢ _ i hx'
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    refine' ⟨(of_open_subsets U).toGlueData.ι i ⟨x, hx⟩, ι_from_open_subsets_glue_apply _ _ _⟩
#align Top.glue_data.range_from_open_subsets_glue TopCat.GlueData.range_from_open_subsets_glue

/-- The gluing of an open cover is homeomomorphic to the original space. -/
def openCoverGlueHomeo (h : (⋃ i, (U i : Set α)) = Set.univ) :
    (ofOpenSubsets U).toGlueData.glued ≃ₜ α :=
  Homeomorph.homeomorphOfContinuousOpen
    (Equiv.ofBijective (fromOpenSubsetsGlue U)
      ⟨from_open_subsets_glue_injective U,
        Set.range_iff_surjective.mp ((range_from_open_subsets_glue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).2 (from_open_subsets_glue_is_open_map U)
#align Top.glue_data.open_cover_glue_homeo TopCat.GlueData.openCoverGlueHomeo

end GlueData

end TopCat

