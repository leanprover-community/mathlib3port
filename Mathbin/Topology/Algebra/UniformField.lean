/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.uniform_field
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformRing
import Mathbin.Topology.Algebra.Field
import Mathbin.FieldTheory.Subfield

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `completable_top_field` which packages the assumptions as a Prop-valued
type class and the main results are the instances `uniform_space.completion.field` and
`uniform_space.completion.topological_division_ring`.
-/


noncomputable section

open Classical uniformity TopologicalSpace

open Set UniformSpace UniformSpace.Completion Filter

variable (K : Type _) [Field K] [UniformSpace K]

-- mathport name: exprhat
local notation "hat" => Completion

/-- A topological field is completable if it is separated and the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure). This ensures the completion is
a field.
-/
class CompletableTopField extends SeparatedSpace K : Prop where
  nice : ∀ F : Filter K, Cauchy F → 𝓝 0 ⊓ F = ⊥ → Cauchy (map (fun x => x⁻¹) F)
#align completable_top_field CompletableTopField

namespace UniformSpace

namespace Completion

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      [(Command.namedPrio "(" "priority" ":=" (num "100") ")")]
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `SeparatedSpace [`K]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `Nontrivial [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(num "0")
           ","
           (num "1")
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`h]
             []
             "=>"
             («term_<|_»
              `zero_ne_one
              "<|"
              (Term.app (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj) [`h]))))]
          "⟩")]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(num "0")
          ","
          (num "1")
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [`h]
            []
            "=>"
            («term_<|_»
             `zero_ne_one
             "<|"
             (Term.app (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj) [`h]))))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(num "0")
        ","
        (num "1")
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          («term_<|_»
           `zero_ne_one
           "<|"
           (Term.app (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj) [`h]))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        («term_<|_»
         `zero_ne_one
         "<|"
         (Term.app (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj) [`h]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `zero_ne_one
       "<|"
       (Term.app (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj) [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `uniform_embedding_coe [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `uniform_embedding_coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `uniform_embedding_coe [`K])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `zero_ne_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Nontrivial [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  [ SeparatedSpace K ] : Nontrivial hat K
  := ⟨ ⟨ 0 , 1 , fun h => zero_ne_one <| uniform_embedding_coe K . inj h ⟩ ⟩

variable {K}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "extension of inversion to the completion of a field. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `hatInv [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
          "→"
          (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `dense_inducing_coe "." `extend)
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
           [(Term.typeSpec ":" `K)]
           "=>"
           (Term.typeAscription
            "("
            (Term.app `coe [(«term_⁻¹» `x "⁻¹")])
            ":"
            [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
            ")")))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `dense_inducing_coe "." `extend)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          [(Term.typeSpec ":" `K)]
          "=>"
          (Term.typeAscription
           "("
           (Term.app `coe [(«term_⁻¹» `x "⁻¹")])
           ":"
           [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
           ")")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        [(Term.typeSpec ":" `K)]
        "=>"
        (Term.typeAscription
         "("
         (Term.app `coe [(«term_⁻¹» `x "⁻¹")])
         ":"
         [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `coe [(«term_⁻¹» `x "⁻¹")])
       ":"
       [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
/-- extension of inversion to the completion of a field. -/
  def hatInv : hat K → hat K := dense_inducing_coe . extend fun x : K => ( coe x ⁻¹ : hat K )
#align uniform_space.completion.hat_inv UniformSpace.Completion.hatInv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `continuous_hat_inv [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `CompletableTopField [`K]) "]")
        (Term.implicitBinder
         "{"
         [`x]
         [":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
         "}")
        (Term.explicitBinder "(" [`h] [":" («term_≠_» `x "≠" (num "0"))] [] ")")]
       (Term.typeSpec ":" (Term.app `ContinuousAt [`hatInv `x])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `T3Space
                 [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]))]
              ":="
              (Term.app `completion.t3_space [`K]))))
           []
           (Tactic.refine'
            "refine'"
            (Term.app `dense_inducing_coe.continuous_at_extend [(Term.hole "_")]))
           []
           (Tactic.apply
            "apply"
            (Term.app `mem_of_superset [(Term.app `compl_singleton_mem_nhds [`h])]))
           []
           (Tactic.intro "intro" [`y `y_ne])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
           []
           (Tactic.apply "apply" `CompleteSpace.complete)
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Filter.map_map)]
             "]")
            [])
           []
           (Tactic.apply
            "apply"
            (Term.app
             `Cauchy.map
             [(Term.hole "_") (Term.app `completion.uniform_continuous_coe [`K])]))
           []
           (Tactic.apply "apply" `CompletableTopField.nice)
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.tacticHaveI_
              "haveI"
              (Term.haveDecl
               (Term.haveIdDecl [] [] ":=" (Term.app `dense_inducing_coe.comap_nhds_ne_bot [`y]))))
             []
             (Tactic.apply "apply" `cauchy_nhds.comap)
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `completion.comap_coe_eq_uniformity)] "]")
                [])
               []
               (Tactic.exact "exact" `le_rfl)])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`eq_bot []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Order.Basic.«term_⊓_»
                    (Term.app
                     (TopologicalSpace.Topology.Basic.nhds "𝓝")
                     [(Term.typeAscription
                       "("
                       (num "0")
                       ":"
                       [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                       ")")])
                    " ⊓ "
                    (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y]))
                   "="
                   (Order.BoundedOrder.«term⊥» "⊥")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.byContra "by_contra" [(Lean.binderIdent `h)])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `y_ne
                      [(Term.proj
                        («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h]))
                        "."
                        `symm)]))]))))))
             []
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  `dense_inducing_coe.nhds_eq_comap
                  [(Term.typeAscription "(" (num "0") ":" [`K] ")")]))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Filter.comap_inf)
                ","
                (Tactic.rwRule [] `eq_bot)]
               "]")
              [])
             []
             (Tactic.exact "exact" `comap_bot)])])))
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
         [(Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app `T3Space [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]))]
             ":="
             (Term.app `completion.t3_space [`K]))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app `dense_inducing_coe.continuous_at_extend [(Term.hole "_")]))
          []
          (Tactic.apply
           "apply"
           (Term.app `mem_of_superset [(Term.app `compl_singleton_mem_nhds [`h])]))
          []
          (Tactic.intro "intro" [`y `y_ne])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
          []
          (Tactic.apply "apply" `CompleteSpace.complete)
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Filter.map_map)]
            "]")
           [])
          []
          (Tactic.apply
           "apply"
           (Term.app
            `Cauchy.map
            [(Term.hole "_") (Term.app `completion.uniform_continuous_coe [`K])]))
          []
          (Tactic.apply "apply" `CompletableTopField.nice)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.tacticHaveI_
             "haveI"
             (Term.haveDecl
              (Term.haveIdDecl [] [] ":=" (Term.app `dense_inducing_coe.comap_nhds_ne_bot [`y]))))
            []
            (Tactic.apply "apply" `cauchy_nhds.comap)
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `completion.comap_coe_eq_uniformity)] "]")
               [])
              []
              (Tactic.exact "exact" `le_rfl)])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`eq_bot []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Order.Basic.«term_⊓_»
                   (Term.app
                    (TopologicalSpace.Topology.Basic.nhds "𝓝")
                    [(Term.typeAscription
                      "("
                      (num "0")
                      ":"
                      [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                      ")")])
                   " ⊓ "
                   (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y]))
                  "="
                  (Order.BoundedOrder.«term⊥» "⊥")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.byContra "by_contra" [(Lean.binderIdent `h)])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `y_ne
                     [(Term.proj
                       («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h]))
                       "."
                       `symm)]))]))))))
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `dense_inducing_coe.nhds_eq_comap
                 [(Term.typeAscription "(" (num "0") ":" [`K] ")")]))
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Filter.comap_inf)
               ","
               (Tactic.rwRule [] `eq_bot)]
              "]")
             [])
            []
            (Tactic.exact "exact" `comap_bot)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`eq_bot []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Order.Basic.«term_⊓_»
               (Term.app
                (TopologicalSpace.Topology.Basic.nhds "𝓝")
                [(Term.typeAscription
                  "("
                  (num "0")
                  ":"
                  [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                  ")")])
               " ⊓ "
               (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y]))
              "="
              (Order.BoundedOrder.«term⊥» "⊥")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.byContra "by_contra" [(Lean.binderIdent `h)])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `y_ne
                 [(Term.proj
                   («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h]))
                   "."
                   `symm)]))]))))))
        []
        (Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `dense_inducing_coe.nhds_eq_comap
             [(Term.typeAscription "(" (num "0") ":" [`K] ")")]))
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Filter.comap_inf)
           ","
           (Tactic.rwRule [] `eq_bot)]
          "]")
         [])
        []
        (Tactic.exact "exact" `comap_bot)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `comap_bot)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comap_bot
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `dense_inducing_coe.nhds_eq_comap
           [(Term.typeAscription "(" (num "0") ":" [`K] ")")]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Filter.comap_inf)
         ","
         (Tactic.rwRule [] `eq_bot)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_bot
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Filter.comap_inf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `dense_inducing_coe.nhds_eq_comap
       [(Term.typeAscription "(" (num "0") ":" [`K] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "0") ":" [`K] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dense_inducing_coe.nhds_eq_comap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`eq_bot []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Order.Basic.«term_⊓_»
             (Term.app
              (TopologicalSpace.Topology.Basic.nhds "𝓝")
              [(Term.typeAscription
                "("
                (num "0")
                ":"
                [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                ")")])
             " ⊓ "
             (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y]))
            "="
            (Order.BoundedOrder.«term⊥» "⊥")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.byContra "by_contra" [(Lean.binderIdent `h)])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `y_ne
               [(Term.proj
                 («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h]))
                 "."
                 `symm)]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.byContra "by_contra" [(Lean.binderIdent `h)])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `y_ne
            [(Term.proj
              («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h]))
              "."
              `symm)]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `y_ne
        [(Term.proj
          («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h]))
          "."
          `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `y_ne
       [(Term.proj («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h])) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h])) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_bot_iff.mpr [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_bot_iff.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `eq_of_nhds_ne_bot
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `eq_of_nhds_ne_bot "<|" (Term.app `ne_bot_iff.mpr [`h]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `y_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.byContra "by_contra" [(Lean.binderIdent `h)])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Order.Basic.«term_⊓_»
        (Term.app
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
           ")")])
        " ⊓ "
        (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y]))
       "="
       (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Order.Basic.«term_⊓_»
       (Term.app
        (TopologicalSpace.Topology.Basic.nhds "𝓝")
        [(Term.typeAscription
          "("
          (num "0")
          ":"
          [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
          ")")])
       " ⊓ "
       (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Term.app
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'
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
  continuous_hat_inv
  [ CompletableTopField K ] { x : hat K } ( h : x ≠ 0 ) : ContinuousAt hatInv x
  :=
    by
      haveI : T3Space hat K := completion.t3_space K
        refine' dense_inducing_coe.continuous_at_extend _
        apply mem_of_superset compl_singleton_mem_nhds h
        intro y y_ne
        rw [ mem_compl_singleton_iff ] at y_ne
        apply CompleteSpace.complete
        rw [ ← Filter.map_map ]
        apply Cauchy.map _ completion.uniform_continuous_coe K
        apply CompletableTopField.nice
        ·
          haveI := dense_inducing_coe.comap_nhds_ne_bot y
            apply cauchy_nhds.comap
            · rw [ completion.comap_coe_eq_uniformity ] exact le_rfl
        ·
          have
              eq_bot
                : 𝓝 ( 0 : hat K ) ⊓ 𝓝 y = ⊥
                :=
                by by_contra h exact y_ne eq_of_nhds_ne_bot <| ne_bot_iff.mpr h . symm
            erw [ dense_inducing_coe.nhds_eq_comap ( 0 : K ) , ← Filter.comap_inf , eq_bot ]
            exact comap_bot
#align uniform_space.completion.continuous_hat_inv UniformSpace.Completion.continuous_hat_inv

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
       (Term.typeSpec
        ":"
        (Term.app `Inv [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (termIfThenElse
            "if"
            («term_=_» `x "=" (num "0"))
            "then"
            (num "0")
            "else"
            (Term.app `hatInv [`x]))))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (termIfThenElse
           "if"
           («term_=_» `x "=" (num "0"))
           "then"
           (num "0")
           "else"
           (Term.app `hatInv [`x]))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (termIfThenElse
         "if"
         («term_=_» `x "=" (num "0"))
         "then"
         (num "0")
         "else"
         (Term.app `hatInv [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termIfThenElse
       "if"
       («term_=_» `x "=" (num "0"))
       "then"
       (num "0")
       "else"
       (Term.app `hatInv [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hatInv [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hatInv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Inv [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Inv hat K := ⟨ fun x => if x = 0 then 0 else hatInv x ⟩

variable [TopologicalDivisionRing K]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `hat_inv_extends [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" `K] "}")
        (Term.explicitBinder "(" [`h] [":" («term_≠_» `x "≠" (num "0"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `hatInv
          [(Term.typeAscription
            "("
            `x
            ":"
            [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
            ")")])
         "="
         (Term.app `coe [(Term.typeAscription "(" («term_⁻¹» `x "⁻¹") ":" [`K] ")")]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `dense_inducing_coe "." `extend_eq_at)
        [(Term.app
          (Term.proj (Term.proj (Term.app `continuous_coe [`K]) "." `ContinuousAt) "." `comp)
          [(Term.app `continuous_at_inv₀ [`h])])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `dense_inducing_coe "." `extend_eq_at)
       [(Term.app
         (Term.proj (Term.proj (Term.app `continuous_coe [`K]) "." `ContinuousAt) "." `comp)
         [(Term.app `continuous_at_inv₀ [`h])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `continuous_coe [`K]) "." `ContinuousAt) "." `comp)
       [(Term.app `continuous_at_inv₀ [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `continuous_at_inv₀ [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_at_inv₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `continuous_at_inv₀ [`h]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `continuous_coe [`K]) "." `ContinuousAt) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `continuous_coe [`K]) "." `ContinuousAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_coe [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `continuous_coe [`K]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj (Term.paren "(" (Term.app `continuous_coe [`K]) ")") "." `ContinuousAt)
       "."
       `comp)
      [(Term.paren "(" (Term.app `continuous_at_inv₀ [`h]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `dense_inducing_coe "." `extend_eq_at)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `dense_inducing_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `hatInv
        [(Term.typeAscription
          "("
          `x
          ":"
          [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
          ")")])
       "="
       (Term.app `coe [(Term.typeAscription "(" («term_⁻¹» `x "⁻¹") ":" [`K] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `coe [(Term.typeAscription "(" («term_⁻¹» `x "⁻¹") ":" [`K] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" («term_⁻¹» `x "⁻¹") ":" [`K] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `x "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `hatInv
       [(Term.typeAscription
         "("
         `x
         ":"
         [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `x
       ":"
       [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  hat_inv_extends
  { x : K } ( h : x ≠ 0 ) : hatInv ( x : hat K ) = coe ( x ⁻¹ : K )
  := dense_inducing_coe . extend_eq_at continuous_coe K . ContinuousAt . comp continuous_at_inv₀ h
#align uniform_space.completion.hat_inv_extends UniformSpace.Completion.hat_inv_extends

variable [CompletableTopField K]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (Std.Tactic.NormCast.Attr.norm_cast "norm_cast" [] []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_inv [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `K] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_⁻¹»
          (Term.typeAscription
           "("
           `x
           ":"
           [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
           ")")
          "⁻¹")
         "="
         (Term.typeAscription
          "("
          (Term.typeAscription "(" («term_⁻¹» `x "⁻¹") ":" [`K] ")")
          ":"
          [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
          ")"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Classical.«tacticBy_cases_:_» "by_cases" [`h ":"] («term_=_» `x "=" (num "0")))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `inv_zero)] "]")
              [])
             []
             (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
             []
             (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
             []
             (Tactic.simp "simp" [] [] [] [] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.Conv.convLHS
              "conv_lhs"
              []
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(Tactic.Conv.dsimp
                  "dsimp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"])])))
             []
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `if_neg)] "]") [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact "exact" (Term.app `hat_inv_extends [`h]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.exact
                "exact"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`H]
                  []
                  "=>"
                  (Term.app `h [(Term.app `dense_embedding_coe.inj [`H])]))))])])])))
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
         [(Classical.«tacticBy_cases_:_» "by_cases" [`h ":"] («term_=_» `x "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `inv_zero)] "]")
             [])
            []
            (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
            []
            (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
            []
            (Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.Conv.convLHS
             "conv_lhs"
             []
             []
             "=>"
             (Tactic.Conv.convSeq
              (Tactic.Conv.convSeq1Indented
               [(Tactic.Conv.dsimp
                 "dsimp"
                 []
                 []
                 []
                 ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"])])))
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `if_neg)] "]") [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `hat_inv_extends [`h]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.fun
                "fun"
                (Term.basicFun
                 [`H]
                 []
                 "=>"
                 (Term.app `h [(Term.app `dense_embedding_coe.inj [`H])]))))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.Conv.convLHS
         "conv_lhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(Tactic.Conv.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"])])))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `if_neg)] "]") [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact "exact" (Term.app `hat_inv_extends [`h]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`H]
             []
             "=>"
             (Term.app `h [(Term.app `dense_embedding_coe.inj [`H])]))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun [`H] [] "=>" (Term.app `h [(Term.app `dense_embedding_coe.inj [`H])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun [`H] [] "=>" (Term.app `h [(Term.app `dense_embedding_coe.inj [`H])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`H] [] "=>" (Term.app `h [(Term.app `dense_embedding_coe.inj [`H])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [(Term.app `dense_embedding_coe.inj [`H])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dense_embedding_coe.inj [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dense_embedding_coe.inj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `dense_embedding_coe.inj [`H])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `hat_inv_extends [`h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hat_inv_extends [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hat_inv_extends [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hat_inv_extends
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `if_neg)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `if_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convLHS
       "conv_lhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Inv.inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `inv_zero)] "]")
         [])
        []
        (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
        []
        (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
        []
        (Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Inv.inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `inv_zero)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_» "by_cases" [`h ":"] («term_=_» `x "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `x "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_⁻¹»
        (Term.typeAscription
         "("
         `x
         ":"
         [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
         ")")
        "⁻¹")
       "="
       (Term.typeAscription
        "("
        (Term.typeAscription "(" («term_⁻¹» `x "⁻¹") ":" [`K] ")")
        ":"
        [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.typeAscription "(" («term_⁻¹» `x "⁻¹") ":" [`K] ")")
       ":"
       [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ norm_cast ]
  theorem
    coe_inv
    ( x : K ) : ( x : hat K ) ⁻¹ = ( ( x ⁻¹ : K ) : hat K )
    :=
      by
        by_cases h : x = 0
          · rw [ h , inv_zero ] dsimp [ Inv.inv ] norm_cast simp
          ·
            conv_lhs => dsimp [ Inv.inv ]
              rw [ if_neg ]
              · exact hat_inv_extends h
              · exact fun H => h dense_embedding_coe.inj H
#align uniform_space.completion.coe_inv UniformSpace.Completion.coe_inv

variable [UniformAddGroup K]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_hat_inv_cancel [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`x]
         [":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
         "}")
        (Term.explicitBinder "(" [`x_ne] [":" («term_≠_» `x "≠" (num "0"))] [] ")")]
       (Term.typeSpec ":" («term_=_» («term_*_» `x "*" (Term.app `hatInv [`x])) "=" (num "1"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticHaveI_
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `T1Space
                 [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]))]
              ":="
              `T2Space.t1_space)))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `f
              []
              []
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                [(Term.typeSpec ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                "=>"
                («term_*_» `x "*" (Term.app `hat_inv [`x])))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c
              []
              []
              ":="
              (Term.typeAscription
               "("
               `coe
               ":"
               [(Term.arrow `K "→" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
               ")"))))
           []
           (Tactic.change "change" («term_=_» (Term.app `f [`x]) "=" (num "1")) [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`cont []]
              [(Term.typeSpec ":" (Term.app `ContinuousAt [`f `x]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.tacticLetI_
                   "letI"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       (Term.app
                        `TopologicalSpace
                        [(«term_×_»
                          (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                          "×"
                          (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]))]
                     ":="
                     `Prod.topologicalSpace)))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       (Term.app
                        `ContinuousAt
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [`y]
                           [(Term.typeSpec
                             ":"
                             (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                           "=>"
                           (Term.typeAscription
                            "("
                            (Term.tuple "(" [`y "," [(Term.app `hat_inv [`y])]] ")")
                            ":"
                            [(«term_×_»
                              (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                              "×"
                              (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                            ")")))
                         `x]))]
                     ":="
                     (Term.app
                      `continuous_id.continuous_at.prod
                      [(Term.app `continuous_hat_inv [`x_ne])]))))
                  []
                  (Tactic.exact
                   "exact"
                   (Term.typeAscription
                    "("
                    (Term.app `_root_.continuous_mul.continuous_at.comp [`this])
                    ":"
                    [(Term.hole "_")]
                    ")"))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`clo []]
              [(Term.typeSpec
                ":"
                («term_∈_»
                 `x
                 "∈"
                 (Term.app
                  `closure
                  [(Set.Data.Set.Image.term_''_
                    `c
                    " '' "
                    (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl [] [] ":=" (Term.app `dense_inducing_coe.dense [`x]))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.show
                       "show"
                       («term_=_»
                        (Term.typeAscription "(" `univ ":" [(Term.app `Set [`K])] ")")
                        "="
                        («term_∪_»
                         («term{_}» "{" [(num "0")] "}")
                         "∪"
                         (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
                       (Term.fromTerm
                        "from"
                        (Term.proj (Term.app `union_compl_self [(Term.hole "_")]) "." `symm))))
                     ","
                     (Tactic.rwRule [] `image_union)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                  []
                  (Tactic.apply "apply" (Term.app `mem_closure_of_mem_closure_union [`this]))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_singleton)] "]")
                   [])
                  []
                  (Tactic.exact "exact" (Term.app `compl_singleton_mem_nhds [`x_ne]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`fxclo []]
              [(Term.typeSpec
                ":"
                («term_∈_»
                 (Term.app `f [`x])
                 "∈"
                 (Term.app
                  `closure
                  [(Set.Data.Set.Image.term_''_
                    `f
                    " '' "
                    (Set.Data.Set.Image.term_''_
                     `c
                     " '' "
                     (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))])))]
              ":="
              (Term.app `mem_closure_image [`cont `clo]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_⊆_»
                 (Set.Data.Set.Image.term_''_
                  `f
                  " '' "
                  (Set.Data.Set.Image.term_''_
                   `c
                   " '' "
                   (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
                 "⊆"
                 («term{_}» "{" [(num "1")] "}")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_image)] "]")
                   [])
                  []
                  (Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
                    (Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_singleton_iff)] "]")
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`z_ne] []))])
                  []
                  (Tactic.dsimp
                   "dsimp"
                   []
                   []
                   []
                   ["[" [(Tactic.simpLemma [] [] `c) "," (Tactic.simpLemma [] [] `f)] "]"]
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `hat_inv_extends [`z_ne]))]
                    "]")
                   [])
                  []
                  (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `mul_inv_cancel [`z_ne]))]
                    "]")
                   [])]))))))
           []
           (Mathlib.Tactic.tacticReplace_
            "replace"
            (Term.haveDecl
             (Term.haveIdDecl [`fxclo []] [] ":=" (Term.app `closure_mono [`this `fxclo]))))
           []
           (Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `closure_singleton) "," (Tactic.rwRule [] `mem_singleton_iff)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`fxclo] []))])])))
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
         [(Std.Tactic.tacticHaveI_
           "haveI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app `T1Space [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]))]
             ":="
             `T2Space.t1_space)))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `f
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               [(Term.typeSpec ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
               "=>"
               («term_*_» `x "*" (Term.app `hat_inv [`x])))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `c
             []
             []
             ":="
             (Term.typeAscription
              "("
              `coe
              ":"
              [(Term.arrow `K "→" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
              ")"))))
          []
          (Tactic.change "change" («term_=_» (Term.app `f [`x]) "=" (num "1")) [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`cont []]
             [(Term.typeSpec ":" (Term.app `ContinuousAt [`f `x]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticLetI_
                  "letI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `TopologicalSpace
                       [(«term_×_»
                         (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                         "×"
                         (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]))]
                    ":="
                    `Prod.topologicalSpace)))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `ContinuousAt
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`y]
                          [(Term.typeSpec
                            ":"
                            (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                          "=>"
                          (Term.typeAscription
                           "("
                           (Term.tuple "(" [`y "," [(Term.app `hat_inv [`y])]] ")")
                           ":"
                           [(«term_×_»
                             (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                             "×"
                             (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                           ")")))
                        `x]))]
                    ":="
                    (Term.app
                     `continuous_id.continuous_at.prod
                     [(Term.app `continuous_hat_inv [`x_ne])]))))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.typeAscription
                   "("
                   (Term.app `_root_.continuous_mul.continuous_at.comp [`this])
                   ":"
                   [(Term.hole "_")]
                   ")"))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`clo []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                `x
                "∈"
                (Term.app
                 `closure
                 [(Set.Data.Set.Image.term_''_
                   `c
                   " '' "
                   (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl [] [] ":=" (Term.app `dense_inducing_coe.dense [`x]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
                    ","
                    (Tactic.rwRule
                     []
                     (Term.show
                      "show"
                      («term_=_»
                       (Term.typeAscription "(" `univ ":" [(Term.app `Set [`K])] ")")
                       "="
                       («term_∪_»
                        («term{_}» "{" [(num "0")] "}")
                        "∪"
                        (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
                      (Term.fromTerm
                       "from"
                       (Term.proj (Term.app `union_compl_self [(Term.hole "_")]) "." `symm))))
                    ","
                    (Tactic.rwRule [] `image_union)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                 []
                 (Tactic.apply "apply" (Term.app `mem_closure_of_mem_closure_union [`this]))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_singleton)] "]")
                  [])
                 []
                 (Tactic.exact "exact" (Term.app `compl_singleton_mem_nhds [`x_ne]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`fxclo []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                (Term.app `f [`x])
                "∈"
                (Term.app
                 `closure
                 [(Set.Data.Set.Image.term_''_
                   `f
                   " '' "
                   (Set.Data.Set.Image.term_''_
                    `c
                    " '' "
                    (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))])))]
             ":="
             (Term.app `mem_closure_image [`cont `clo]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_⊆_»
                (Set.Data.Set.Image.term_''_
                 `f
                 " '' "
                 (Set.Data.Set.Image.term_''_
                  `c
                  " '' "
                  (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
                "⊆"
                («term{_}» "{" [(num "1")] "}")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_image)] "]")
                  [])
                 []
                 (Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_singleton_iff)] "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`z_ne] []))])
                 []
                 (Tactic.dsimp
                  "dsimp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [] `c) "," (Tactic.simpLemma [] [] `f)] "]"]
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `hat_inv_extends [`z_ne]))]
                   "]")
                  [])
                 []
                 (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_inv_cancel [`z_ne]))] "]")
                  [])]))))))
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl [`fxclo []] [] ":=" (Term.app `closure_mono [`this `fxclo]))))
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `closure_singleton) "," (Tactic.rwRule [] `mem_singleton_iff)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`fxclo] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `closure_singleton) "," (Tactic.rwRule [] `mem_singleton_iff)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`fxclo] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fxclo
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `closure_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl [`fxclo []] [] ":=" (Term.app `closure_mono [`this `fxclo]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `closure_mono [`this `fxclo])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `fxclo
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closure_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_⊆_»
            (Set.Data.Set.Image.term_''_
             `f
             " '' "
             (Set.Data.Set.Image.term_''_
              `c
              " '' "
              (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
            "⊆"
            («term{_}» "{" [(num "1")] "}")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_image)] "]") [])
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_singleton_iff)] "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`z_ne] []))])
             []
             (Tactic.dsimp
              "dsimp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `c) "," (Tactic.simpLemma [] [] `f)] "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hat_inv_extends [`z_ne]))] "]")
              [])
             []
             (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_inv_cancel [`z_ne]))] "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_image)] "]") [])
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_singleton_iff)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`z_ne] []))])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `c) "," (Tactic.simpLemma [] [] `f)] "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hat_inv_extends [`z_ne]))] "]")
           [])
          []
          (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_inv_cancel [`z_ne]))] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mul_inv_cancel [`z_ne]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_inv_cancel [`z_ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_inv_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `hat_inv_extends [`z_ne]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hat_inv_extends [`z_ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hat_inv_extends
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `c) "," (Tactic.simpLemma [] [] `f)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`z_ne] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_compl_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_singleton_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_image)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_image
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_»
       (Set.Data.Set.Image.term_''_
        `f
        " '' "
        (Set.Data.Set.Image.term_''_
         `c
         " '' "
         (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
       "⊆"
       («term{_}» "{" [(num "1")] "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [(num "1")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.Data.Set.Image.term_''_
       `f
       " '' "
       (Set.Data.Set.Image.term_''_
        `c
        " '' "
        (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       `c
       " '' "
       (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
      («term{_}» "{" [(num "0")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none,
     [anonymous]) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 999, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      `c
      " '' "
      (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 81, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`fxclo []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            (Term.app `f [`x])
            "∈"
            (Term.app
             `closure
             [(Set.Data.Set.Image.term_''_
               `f
               " '' "
               (Set.Data.Set.Image.term_''_
                `c
                " '' "
                (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))])))]
         ":="
         (Term.app `mem_closure_image [`cont `clo]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_closure_image [`cont `clo])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `clo
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cont
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_closure_image
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.app `f [`x])
       "∈"
       (Term.app
        `closure
        [(Set.Data.Set.Image.term_''_
          `f
          " '' "
          (Set.Data.Set.Image.term_''_
           `c
           " '' "
           (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `closure
       [(Set.Data.Set.Image.term_''_
         `f
         " '' "
         (Set.Data.Set.Image.term_''_
          `c
          " '' "
          (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       `f
       " '' "
       (Set.Data.Set.Image.term_''_
        `c
        " '' "
        (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       `c
       " '' "
       (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
      («term{_}» "{" [(num "0")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none,
     [anonymous]) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 999, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      `c
      " '' "
      (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      `f
      " '' "
      (Term.paren
       "("
       (Set.Data.Set.Image.term_''_
        `c
        " '' "
        (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
       ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
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
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`clo []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            `x
            "∈"
            (Term.app
             `closure
             [(Set.Data.Set.Image.term_''_
               `c
               " '' "
               (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl [] [] ":=" (Term.app `dense_inducing_coe.dense [`x]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
                ","
                (Tactic.rwRule
                 []
                 (Term.show
                  "show"
                  («term_=_»
                   (Term.typeAscription "(" `univ ":" [(Term.app `Set [`K])] ")")
                   "="
                   («term_∪_»
                    («term{_}» "{" [(num "0")] "}")
                    "∪"
                    (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
                  (Term.fromTerm
                   "from"
                   (Term.proj (Term.app `union_compl_self [(Term.hole "_")]) "." `symm))))
                ","
                (Tactic.rwRule [] `image_union)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
             []
             (Tactic.apply "apply" (Term.app `mem_closure_of_mem_closure_union [`this]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_singleton)] "]")
              [])
             []
             (Tactic.exact "exact" (Term.app `compl_singleton_mem_nhds [`x_ne]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `dense_inducing_coe.dense [`x]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
             ","
             (Tactic.rwRule
              []
              (Term.show
               "show"
               («term_=_»
                (Term.typeAscription "(" `univ ":" [(Term.app `Set [`K])] ")")
                "="
                («term_∪_»
                 («term{_}» "{" [(num "0")] "}")
                 "∪"
                 (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
               (Term.fromTerm
                "from"
                (Term.proj (Term.app `union_compl_self [(Term.hole "_")]) "." `symm))))
             ","
             (Tactic.rwRule [] `image_union)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.apply "apply" (Term.app `mem_closure_of_mem_closure_union [`this]))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_singleton)] "]") [])
          []
          (Tactic.exact "exact" (Term.app `compl_singleton_mem_nhds [`x_ne]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `compl_singleton_mem_nhds [`x_ne]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `compl_singleton_mem_nhds [`x_ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `compl_singleton_mem_nhds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `image_singleton)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `mem_closure_of_mem_closure_union [`this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_closure_of_mem_closure_union [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_closure_of_mem_closure_union
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `image_univ)
         ","
         (Tactic.rwRule
          []
          (Term.show
           "show"
           («term_=_»
            (Term.typeAscription "(" `univ ":" [(Term.app `Set [`K])] ")")
            "="
            («term_∪_»
             («term{_}» "{" [(num "0")] "}")
             "∪"
             (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
           (Term.fromTerm
            "from"
            (Term.proj (Term.app `union_compl_self [(Term.hole "_")]) "." `symm))))
         ","
         (Tactic.rwRule [] `image_union)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_union
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.typeAscription "(" `univ ":" [(Term.app `Set [`K])] ")")
        "="
        («term_∪_»
         («term{_}» "{" [(num "0")] "}")
         "∪"
         (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
       (Term.fromTerm "from" (Term.proj (Term.app `union_compl_self [(Term.hole "_")]) "." `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `union_compl_self [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `union_compl_self [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `union_compl_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `union_compl_self [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription "(" `univ ":" [(Term.app `Set [`K])] ")")
       "="
       («term_∪_»
        («term{_}» "{" [(num "0")] "}")
        "∪"
        (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∪_»
       («term{_}» "{" [(num "0")] "}")
       "∪"
       (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
      («term{_}» "{" [(num "0")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none,
     [anonymous]) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 999, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term{_}» "{" [(num "0")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `univ ":" [(Term.app `Set [`K])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `dense_inducing_coe.dense [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dense_inducing_coe.dense [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dense_inducing_coe.dense
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `x
       "∈"
       (Term.app
        `closure
        [(Set.Data.Set.Image.term_''_
          `c
          " '' "
          (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `closure
       [(Set.Data.Set.Image.term_''_
         `c
         " '' "
         (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       `c
       " '' "
       (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
      («term{_}» "{" [(num "0")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none,
     [anonymous]) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 999, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      `c
      " '' "
      (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`cont []]
         [(Term.typeSpec ":" (Term.app `ContinuousAt [`f `x]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticLetI_
              "letI"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Term.app
                   `TopologicalSpace
                   [(«term_×_»
                     (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                     "×"
                     (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]))]
                ":="
                `Prod.topologicalSpace)))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Term.app
                   `ContinuousAt
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`y]
                      [(Term.typeSpec
                        ":"
                        (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                      "=>"
                      (Term.typeAscription
                       "("
                       (Term.tuple "(" [`y "," [(Term.app `hat_inv [`y])]] ")")
                       ":"
                       [(«term_×_»
                         (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                         "×"
                         (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                       ")")))
                    `x]))]
                ":="
                (Term.app
                 `continuous_id.continuous_at.prod
                 [(Term.app `continuous_hat_inv [`x_ne])]))))
             []
             (Tactic.exact
              "exact"
              (Term.typeAscription
               "("
               (Term.app `_root_.continuous_mul.continuous_at.comp [`this])
               ":"
               [(Term.hole "_")]
               ")"))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `TopologicalSpace
                [(«term_×_»
                  (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                  "×"
                  (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]))]
             ":="
             `Prod.topologicalSpace)))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `ContinuousAt
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`y]
                   [(Term.typeSpec
                     ":"
                     (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                   "=>"
                   (Term.typeAscription
                    "("
                    (Term.tuple "(" [`y "," [(Term.app `hat_inv [`y])]] ")")
                    ":"
                    [(«term_×_»
                      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                      "×"
                      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                    ")")))
                 `x]))]
             ":="
             (Term.app
              `continuous_id.continuous_at.prod
              [(Term.app `continuous_hat_inv [`x_ne])]))))
          []
          (Tactic.exact
           "exact"
           (Term.typeAscription
            "("
            (Term.app `_root_.continuous_mul.continuous_at.comp [`this])
            ":"
            [(Term.hole "_")]
            ")"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.typeAscription
        "("
        (Term.app `_root_.continuous_mul.continuous_at.comp [`this])
        ":"
        [(Term.hole "_")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `_root_.continuous_mul.continuous_at.comp [`this])
       ":"
       [(Term.hole "_")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `_root_.continuous_mul.continuous_at.comp [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `_root_.continuous_mul.continuous_at.comp
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
         []
         [(Term.typeSpec
           ":"
           (Term.app
            `ContinuousAt
            [(Term.fun
              "fun"
              (Term.basicFun
               [`y]
               [(Term.typeSpec ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
               "=>"
               (Term.typeAscription
                "("
                (Term.tuple "(" [`y "," [(Term.app `hat_inv [`y])]] ")")
                ":"
                [(«term_×_»
                  (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
                  "×"
                  (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
                ")")))
             `x]))]
         ":="
         (Term.app `continuous_id.continuous_at.prod [(Term.app `continuous_hat_inv [`x_ne])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `continuous_id.continuous_at.prod [(Term.app `continuous_hat_inv [`x_ne])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `continuous_hat_inv [`x_ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_hat_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_hat_inv [`x_ne])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_id.continuous_at.prod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ContinuousAt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`y]
          [(Term.typeSpec ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
          "=>"
          (Term.typeAscription
           "("
           (Term.tuple "(" [`y "," [(Term.app `hat_inv [`y])]] ")")
           ":"
           [(«term_×_»
             (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
             "×"
             (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
           ")")))
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
        [`y]
        [(Term.typeSpec ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
        "=>"
        (Term.typeAscription
         "("
         (Term.tuple "(" [`y "," [(Term.app `hat_inv [`y])]] ")")
         ":"
         [(«term_×_»
           (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
           "×"
           (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.tuple "(" [`y "," [(Term.app `hat_inv [`y])]] ")")
       ":"
       [(«term_×_»
         (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
         "×"
         (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
       "×"
       (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
  mul_hat_inv_cancel
  { x : hat K } ( x_ne : x ≠ 0 ) : x * hatInv x = 1
  :=
    by
      haveI : T1Space hat K := T2Space.t1_space
        let f := fun x : hat K => x * hat_inv x
        let c := ( coe : K → hat K )
        change f x = 1
        have
          cont
            : ContinuousAt f x
            :=
            by
              letI : TopologicalSpace hat K × hat K := Prod.topologicalSpace
                have
                  : ContinuousAt fun y : hat K => ( ( y , hat_inv y ) : hat K × hat K ) x
                    :=
                    continuous_id.continuous_at.prod continuous_hat_inv x_ne
                exact ( _root_.continuous_mul.continuous_at.comp this : _ )
        have
          clo
            : x ∈ closure c '' { 0 } ᶜ
            :=
            by
              have := dense_inducing_coe.dense x
                rw
                  [
                    ← image_univ
                      ,
                      show ( univ : Set K ) = { 0 } ∪ { 0 } ᶜ from union_compl_self _ . symm
                      ,
                      image_union
                    ]
                  at this
                apply mem_closure_of_mem_closure_union this
                rw [ image_singleton ]
                exact compl_singleton_mem_nhds x_ne
        have fxclo : f x ∈ closure f '' c '' { 0 } ᶜ := mem_closure_image cont clo
        have
          : f '' c '' { 0 } ᶜ ⊆ { 1 }
            :=
            by
              rw [ image_image ]
                rintro _ ⟨ z , z_ne , rfl ⟩
                rw [ mem_singleton_iff ]
                rw [ mem_compl_singleton_iff ] at z_ne
                dsimp [ c , f ]
                rw [ hat_inv_extends z_ne ]
                norm_cast
                rw [ mul_inv_cancel z_ne ]
        replace fxclo := closure_mono this fxclo
        rwa [ closure_singleton , mem_singleton_iff ] at fxclo
#align uniform_space.completion.mul_hat_inv_cancel UniformSpace.Completion.mul_hat_inv_cancel

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
       (Term.typeSpec
        ":"
        (Term.app `Field [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Completion.hasInv
          ","
          (Term.typeAscription
           "("
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))
           ":"
           [(Term.app `CommRing [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])])]
           ")")]
         "with"]
        [(Term.structInstField
          (Term.structInstLVal `exists_pair_ne [])
          ":="
          (Term.anonymousCtor
           "⟨"
           [(num "0")
            ","
            (num "1")
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [`h]
              []
              "=>"
              (Term.app
               `zero_ne_one
               [(Term.app (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj) [`h])])))]
           "⟩"))
         []
         (Term.structInstField
          (Term.structInstLVal `mul_inv_cancel [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `x_ne]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 []
                 ["["
                  [(Tactic.simpLemma [] [] (Term.app `if_neg [`x_ne]))
                   ","
                   (Tactic.simpLemma [] [] (Term.app `mul_hat_inv_cancel [`x_ne]))]
                  "]"]
                 [])]))))))
         []
         (Term.structInstField
          (Term.structInstLVal `inv_zero [])
          ":="
          (Term.show
           "show"
           («term_=_»
            («term_⁻¹»
             (Term.typeAscription
              "("
              (Term.typeAscription "(" (num "0") ":" [`K] ")")
              ":"
              [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
              ")")
             "⁻¹")
            "="
            (Term.typeAscription
             "("
             (Term.typeAscription "(" (num "0") ":" [`K] ")")
             ":"
             [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
             ")"))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `coe_inv) "," (Tactic.rwRule [] `inv_zero)]
                 "]")
                [])])))))]
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
       [[`Completion.hasInv
         ","
         (Term.typeAscription
          "("
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))
          ":"
          [(Term.app `CommRing [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])])]
          ")")]
        "with"]
       [(Term.structInstField
         (Term.structInstLVal `exists_pair_ne [])
         ":="
         (Term.anonymousCtor
          "⟨"
          [(num "0")
           ","
           (num "1")
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [`h]
             []
             "=>"
             (Term.app
              `zero_ne_one
              [(Term.app (Term.proj (Term.app `uniform_embedding_coe [`K]) "." `inj) [`h])])))]
          "⟩"))
        []
        (Term.structInstField
         (Term.structInstLVal `mul_inv_cancel [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `x_ne]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] (Term.app `if_neg [`x_ne]))
                  ","
                  (Tactic.simpLemma [] [] (Term.app `mul_hat_inv_cancel [`x_ne]))]
                 "]"]
                [])]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `inv_zero [])
         ":="
         (Term.show
          "show"
          («term_=_»
           («term_⁻¹»
            (Term.typeAscription
             "("
             (Term.typeAscription "(" (num "0") ":" [`K] ")")
             ":"
             [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
             ")")
            "⁻¹")
           "="
           (Term.typeAscription
            "("
            (Term.typeAscription "(" (num "0") ":" [`K] ")")
            ":"
            [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
            ")"))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `coe_inv) "," (Tactic.rwRule [] `inv_zero)]
                "]")
               [])])))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        («term_⁻¹»
         (Term.typeAscription
          "("
          (Term.typeAscription "(" (num "0") ":" [`K] ")")
          ":"
          [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
          ")")
         "⁻¹")
        "="
        (Term.typeAscription
         "("
         (Term.typeAscription "(" (num "0") ":" [`K] ")")
         ":"
         [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
         ")"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `coe_inv) "," (Tactic.rwRule [] `inv_zero)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `coe_inv) "," (Tactic.rwRule [] `inv_zero)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_⁻¹»
        (Term.typeAscription
         "("
         (Term.typeAscription "(" (num "0") ":" [`K] ")")
         ":"
         [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
         ")")
        "⁻¹")
       "="
       (Term.typeAscription
        "("
        (Term.typeAscription "(" (num "0") ":" [`K] ")")
        ":"
        [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.typeAscription "(" (num "0") ":" [`K] ")")
       ":"
       [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : Field hat K
  :=
    {
      Completion.hasInv , ( by infer_instance : CommRing hat K ) with
      exists_pair_ne := ⟨ 0 , 1 , fun h => zero_ne_one uniform_embedding_coe K . inj h ⟩
        mul_inv_cancel
          :=
          fun x x_ne => by dsimp [ Inv.inv ] simp [ if_neg x_ne , mul_hat_inv_cancel x_ne ]
        inv_zero
          :=
          show ( ( 0 : K ) : hat K ) ⁻¹ = ( ( 0 : K ) : hat K ) by rw [ coe_inv , inv_zero ]
      }

/- failed to parenthesize: unknown constant 'group'
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `TopologicalDivisionRing
         [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Completion.top_ring_compl] "with"]
        [(Term.structInstField
          (Term.structInstLVal `continuous_at_inv₀ [])
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.intro "intro" [`x `x_ne])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   («term_∈_»
                    (Set.«term{_|_}»
                     "{"
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
                     "|"
                     («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
                     "}")
                    "∈"
                    (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])))]
                 ":="
                 (Std.Tactic.haveI
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_⊆_»
                       (Order.Basic.«term_ᶜ»
                        («term{_}»
                         "{"
                         [(Term.typeAscription
                           "("
                           (num "0")
                           ":"
                           [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                           ")")]
                         "}")
                        "ᶜ")
                       "⊆"
                       (Set.«term{_|_}»
                        "{"
                        (Std.ExtendedBinder.extBinder
                         (Lean.binderIdent `y)
                         [(group
                           ":"
                           (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))])
                        "|"
                        («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
                        "}")))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.intro "intro" [`y `y_ne])
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                         [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
                        []
                        (Tactic.dsimp
                         "dsimp"
                         []
                         []
                         []
                         ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"]
                         [])
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `if_neg [`y_ne]))] "]")
                         [])])))))
                  []
                  (Term.app
                   `mem_of_superset
                   [(Term.app `compl_singleton_mem_nhds [`x_ne]) `this])))))
              []
              (Tactic.exact
               "exact"
               (Term.app `ContinuousAt.congr [(Term.app `continuous_hat_inv [`x_ne]) `this]))]))))]
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
       [[`Completion.top_ring_compl] "with"]
       [(Term.structInstField
         (Term.structInstLVal `continuous_at_inv₀ [])
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`x `x_ne])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   (Set.«term{_|_}»
                    "{"
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
                    "|"
                    («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
                    "}")
                   "∈"
                   (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])))]
                ":="
                (Std.Tactic.haveI
                 "haveI"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_⊆_»
                      (Order.Basic.«term_ᶜ»
                       («term{_}»
                        "{"
                        [(Term.typeAscription
                          "("
                          (num "0")
                          ":"
                          [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                          ")")]
                        "}")
                       "ᶜ")
                      "⊆"
                      (Set.«term{_|_}»
                       "{"
                       (Std.ExtendedBinder.extBinder
                        (Lean.binderIdent `y)
                        [(group ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))])
                       "|"
                       («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
                       "}")))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.intro "intro" [`y `y_ne])
                       []
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
                       []
                       (Tactic.dsimp
                        "dsimp"
                        []
                        []
                        []
                        ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"]
                        [])
                       []
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `if_neg [`y_ne]))] "]")
                        [])])))))
                 []
                 (Term.app
                  `mem_of_superset
                  [(Term.app `compl_singleton_mem_nhds [`x_ne]) `this])))))
             []
             (Tactic.exact
              "exact"
              (Term.app `ContinuousAt.congr [(Term.app `continuous_hat_inv [`x_ne]) `this]))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`x `x_ne])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_∈_»
                (Set.«term{_|_}»
                 "{"
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
                 "|"
                 («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
                 "}")
                "∈"
                (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])))]
             ":="
             (Std.Tactic.haveI
              "haveI"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_⊆_»
                   (Order.Basic.«term_ᶜ»
                    («term{_}»
                     "{"
                     [(Term.typeAscription
                       "("
                       (num "0")
                       ":"
                       [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                       ")")]
                     "}")
                    "ᶜ")
                   "⊆"
                   (Set.«term{_|_}»
                    "{"
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `y)
                     [(group ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))])
                    "|"
                    («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
                    "}")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.intro "intro" [`y `y_ne])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
                    []
                    (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `if_neg [`y_ne]))] "]")
                     [])])))))
              []
              (Term.app `mem_of_superset [(Term.app `compl_singleton_mem_nhds [`x_ne]) `this])))))
          []
          (Tactic.exact
           "exact"
           (Term.app `ContinuousAt.congr [(Term.app `continuous_hat_inv [`x_ne]) `this]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `ContinuousAt.congr [(Term.app `continuous_hat_inv [`x_ne]) `this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ContinuousAt.congr [(Term.app `continuous_hat_inv [`x_ne]) `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_hat_inv [`x_ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_hat_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_hat_inv [`x_ne])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousAt.congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_∈_»
            (Set.«term{_|_}»
             "{"
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `y) [])
             "|"
             («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
             "}")
            "∈"
            (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])))]
         ":="
         (Std.Tactic.haveI
          "haveI"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_⊆_»
               (Order.Basic.«term_ᶜ»
                («term{_}»
                 "{"
                 [(Term.typeAscription
                   "("
                   (num "0")
                   ":"
                   [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                   ")")]
                 "}")
                "ᶜ")
               "⊆"
               (Set.«term{_|_}»
                "{"
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `y)
                 [(group ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))])
                "|"
                («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
                "}")))]
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.intro "intro" [`y `y_ne])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
                []
                (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `if_neg [`y_ne]))] "]")
                 [])])))))
          []
          (Term.app `mem_of_superset [(Term.app `compl_singleton_mem_nhds [`x_ne]) `this])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.haveI
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_⊆_»
            (Order.Basic.«term_ᶜ»
             («term{_}»
              "{"
              [(Term.typeAscription
                "("
                (num "0")
                ":"
                [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
                ")")]
              "}")
             "ᶜ")
            "⊆"
            (Set.«term{_|_}»
             "{"
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `y)
              [(group ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))])
             "|"
             («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
             "}")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`y `y_ne])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
             []
             (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `if_neg [`y_ne]))] "]")
              [])])))))
       []
       (Term.app `mem_of_superset [(Term.app `compl_singleton_mem_nhds [`x_ne]) `this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_of_superset [(Term.app `compl_singleton_mem_nhds [`x_ne]) `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `compl_singleton_mem_nhds [`x_ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `compl_singleton_mem_nhds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `compl_singleton_mem_nhds [`x_ne])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_of_superset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`y `y_ne])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
          []
          (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `if_neg [`y_ne]))] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `if_neg [`y_ne]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `if_neg [`y_ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `if_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Inv.inv)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Inv.inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`y_ne] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_compl_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`y `y_ne])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_»
       (Order.Basic.«term_ᶜ»
        («term{_}»
         "{"
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])]
           ")")]
         "}")
        "ᶜ")
       "⊆"
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `y)
         [(group ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))])
        "|"
        («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder
        (Lean.binderIdent `y)
        [(group ":" (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K]))])
       "|"
       («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `hat_inv [`y]) "=" («term_⁻¹» `y "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `y "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `hat_inv [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hat_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Topology.Algebra.UniformField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Topology.Algebra.UniformField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.UniformField.termhat', expected 'Topology.Algebra.UniformField.termhat._@.Topology.Algebra.UniformField._hyg.6'-/-- failed to format: unknown constant 'group'
instance
  : TopologicalDivisionRing hat K
  :=
    {
      Completion.top_ring_compl with
      continuous_at_inv₀
        :=
        by
          intro x x_ne
            have
              : { y | hat_inv y = y ⁻¹ } ∈ 𝓝 x
                :=
                haveI
                  : { ( 0 : hat K ) } ᶜ ⊆ { y : hat K | hat_inv y = y ⁻¹ }
                    :=
                    by
                      intro y y_ne
                        rw [ mem_compl_singleton_iff ] at y_ne
                        dsimp [ Inv.inv ]
                        rw [ if_neg y_ne ]
                  mem_of_superset compl_singleton_mem_nhds x_ne this
            exact ContinuousAt.congr continuous_hat_inv x_ne this
      }

end Completion

end UniformSpace

variable (L : Type _) [Field L] [UniformSpace L] [CompletableTopField L]

instance Subfield.completable_top_field (K : Subfield L) : CompletableTopField K :=
  { Subtype.separated_space (K : Set L) with
    nice := by
      intro F F_cau inf_F
      let i : K →+* L := K.subtype
      have hi : UniformInducing i := uniform_embedding_subtype_coe.to_uniform_inducing
      rw [← hi.cauchy_map_iff] at F_cau⊢
      rw [map_comm
          (show (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i
            by
            ext
            rfl)]
      apply CompletableTopField.nice _ F_cau
      rw [← Filter.push_pull', ← map_zero i, ← hi.inducing.nhds_eq_comap, inf_F, Filter.map_bot] }
#align subfield.completable_top_field Subfield.completable_top_field

instance (priority := 100) completable_top_field_of_complete (L : Type _) [Field L] [UniformSpace L]
    [TopologicalDivisionRing L] [SeparatedSpace L] [CompleteSpace L] : CompletableTopField L :=
  { ‹SeparatedSpace L› with
    nice := fun F cau_F hF => by
      haveI : ne_bot F := cau_F.1
      rcases CompleteSpace.complete cau_F with ⟨x, hx⟩
      have hx' : x ≠ 0 := by
        rintro rfl
        rw [inf_eq_right.mpr hx] at hF
        exact cau_F.1.Ne hF
      exact
        Filter.Tendsto.cauchy_map
          (calc
            map (fun x => x⁻¹) F ≤ map (fun x => x⁻¹) (𝓝 x) := map_mono hx
            _ ≤ 𝓝 x⁻¹ := continuous_at_inv₀ hx'
            ) }
#align completable_top_field_of_complete completable_top_field_of_complete

