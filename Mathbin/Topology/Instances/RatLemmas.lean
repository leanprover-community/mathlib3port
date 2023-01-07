/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.instances.rat_lemmas
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Irrational
import Mathbin.Topology.Instances.Rat
import Mathbin.Topology.Alexandroff

/-!
# Additional lemmas about the topology on rational numbers

The structure of a metric space on `ℚ` (`rat.metric_space`) is introduced elsewhere, induced from
`ℝ`. In this file we prove some properties of this topological space and its one-point
compactification.

## Main statements

- `rat.totally_disconnected_space`: `ℚ` is a totally disconnected space;

- `rat.not_countably_generated_nhds_infty_alexandroff`: the filter of neighbourhoods of infinity in
  `alexandroff ℚ` is not countably generated.

## Notation

- `ℚ∞` is used as a local notation for `alexandroff ℚ`
-/


open Set Metric Filter TopologicalSpace

open TopologicalSpace Alexandroff

-- mathport name: «exprℚ∞»
local notation "ℚ∞" => Alexandroff ℚ

namespace Rat

variable {p q : ℚ} {s t : Set ℚ}

theorem interior_compact_eq_empty (hs : IsCompact s) : interior s = ∅ :=
  dense_embedding_coe_real.to_dense_inducing.interior_compact_eq_empty dense_irrational hs
#align rat.interior_compact_eq_empty Rat.interior_compact_eq_empty

theorem dense_compl_compact (hs : IsCompact s) : Dense (sᶜ) :=
  interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)
#align rat.dense_compl_compact Rat.dense_compl_compact

instance cocompact_inf_nhds_ne_bot : NeBot (cocompact ℚ ⊓ 𝓝 p) :=
  by
  refine' (has_basis_cocompact.inf (nhds_basis_opens _)).ne_bot_iff.2 _
  rintro ⟨s, o⟩ ⟨hs, hpo, ho⟩; rw [inter_comm]
  exact (dense_compl_compact hs).inter_open_nonempty _ ho ⟨p, hpo⟩
#align rat.cocompact_inf_nhds_ne_bot Rat.cocompact_inf_nhds_ne_bot

theorem not_countably_generated_cocompact : ¬IsCountablyGenerated (cocompact ℚ) :=
  by
  intro H
  rcases exists_seq_tendsto (cocompact ℚ ⊓ 𝓝 0) with ⟨x, hx⟩
  rw [tendsto_inf] at hx; rcases hx with ⟨hxc, hx0⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x n ∉ insert (0 : ℚ) (range x)
  exact (hxc.eventually hx0.is_compact_insert_range.compl_mem_cocompact).exists
  exact hn (Or.inr ⟨n, rfl⟩)
#align rat.not_countably_generated_cocompact Rat.not_countably_generated_cocompact

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `not_countably_generated_nhds_infty_alexandroff [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term¬_»
         "¬"
         (Term.app
          `IsCountablyGenerated
          [(Term.app
            (TopologicalSpace.Topology.Basic.nhds "𝓝")
            [(Term.typeAscription
              "("
              (Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")
              ":"
              [(Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")]
              ")")])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `is_countably_generated
                 [(Term.app
                   `comap
                   [(Term.typeAscription
                     "("
                     `coe
                     ":"
                     [(Term.arrow
                       (Data.Rat.Init.termℚ "ℚ")
                       "→"
                       (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞"))]
                     ")")
                    (Term.app
                     (TopologicalSpace.Topology.Basic.nhds "𝓝")
                     [(Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")])])]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Alexandroff.comap_coe_nhds_infty)
              ","
              (Tactic.rwRule [] `coclosed_compact_eq_cocompact)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.exact "exact" (Term.app `not_countably_generated_cocompact [`this]))])))
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
         [(Tactic.intro "intro" [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `is_countably_generated
                [(Term.app
                  `comap
                  [(Term.typeAscription
                    "("
                    `coe
                    ":"
                    [(Term.arrow
                      (Data.Rat.Init.termℚ "ℚ")
                      "→"
                      (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞"))]
                    ")")
                   (Term.app
                    (TopologicalSpace.Topology.Basic.nhds "𝓝")
                    [(Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")])])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Alexandroff.comap_coe_nhds_infty)
             ","
             (Tactic.rwRule [] `coclosed_compact_eq_cocompact)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.exact "exact" (Term.app `not_countably_generated_cocompact [`this]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `not_countably_generated_cocompact [`this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_countably_generated_cocompact [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_countably_generated_cocompact
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
        [(Tactic.rwRule [] `Alexandroff.comap_coe_nhds_infty)
         ","
         (Tactic.rwRule [] `coclosed_compact_eq_cocompact)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coclosed_compact_eq_cocompact
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Alexandroff.comap_coe_nhds_infty
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
            `is_countably_generated
            [(Term.app
              `comap
              [(Term.typeAscription
                "("
                `coe
                ":"
                [(Term.arrow
                  (Data.Rat.Init.termℚ "ℚ")
                  "→"
                  (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞"))]
                ")")
               (Term.app
                (TopologicalSpace.Topology.Basic.nhds "𝓝")
                [(Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")])])]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_countably_generated
       [(Term.app
         `comap
         [(Term.typeAscription
           "("
           `coe
           ":"
           [(Term.arrow (Data.Rat.Init.termℚ "ℚ") "→" (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞"))]
           ")")
          (Term.app
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           [(Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `comap
       [(Term.typeAscription
         "("
         `coe
         ":"
         [(Term.arrow (Data.Rat.Init.termℚ "ℚ") "→" (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞"))]
         ")")
        (Term.app
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         [(Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       [(Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Alexandroff.Topology.Alexandroff.alexandroff.infty', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Alexandroff.Topology.Alexandroff.alexandroff.infty', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
      [(Alexandroff.Topology.Alexandroff.alexandroff.infty "∞")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       `coe
       ":"
       [(Term.arrow (Data.Rat.Init.termℚ "ℚ") "→" (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Data.Rat.Init.termℚ "ℚ") "→" (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Instances.RatLemmas.«termℚ∞»', expected 'Topology.Instances.RatLemmas.termℚ∞._@.Topology.Instances.RatLemmas._hyg.6'
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
  not_countably_generated_nhds_infty_alexandroff
  : ¬ IsCountablyGenerated 𝓝 ( ∞ : ℚ∞ )
  :=
    by
      intro
        have : is_countably_generated comap ( coe : ℚ → ℚ∞ ) 𝓝 ∞ := by infer_instance
        rw [ Alexandroff.comap_coe_nhds_infty , coclosed_compact_eq_cocompact ] at this
        exact not_countably_generated_cocompact this
#align
  rat.not_countably_generated_nhds_infty_alexandroff Rat.not_countably_generated_nhds_infty_alexandroff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `not_first_countable_topology_alexandroff [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term¬_»
         "¬"
         (Term.app `FirstCountableTopology [(Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [])
           []
           (Tactic.exact
            "exact"
            (Term.app `not_countably_generated_nhds_infty_alexandroff [`inferInstance]))])))
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
         [(Tactic.intro "intro" [])
          []
          (Tactic.exact
           "exact"
           (Term.app `not_countably_generated_nhds_infty_alexandroff [`inferInstance]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `not_countably_generated_nhds_infty_alexandroff [`inferInstance]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_countably_generated_nhds_infty_alexandroff [`inferInstance])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_countably_generated_nhds_infty_alexandroff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term¬_»
       "¬"
       (Term.app `FirstCountableTopology [(Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `FirstCountableTopology [(Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Instances.RatLemmas.«termℚ∞»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Instances.RatLemmas.«termℚ∞»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Instances.RatLemmas.«termℚ∞»', expected 'Topology.Instances.RatLemmas.termℚ∞._@.Topology.Instances.RatLemmas._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  not_first_countable_topology_alexandroff
  : ¬ FirstCountableTopology ℚ∞
  := by intro exact not_countably_generated_nhds_infty_alexandroff inferInstance
#align rat.not_first_countable_topology_alexandroff Rat.not_first_countable_topology_alexandroff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `not_second_countable_topology_alexandroff [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term¬_»
         "¬"
         (Term.app `SecondCountableTopology [(Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [])
           []
           (Tactic.exact
            "exact"
            (Term.app `not_first_countable_topology_alexandroff [`inferInstance]))])))
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
         [(Tactic.intro "intro" [])
          []
          (Tactic.exact
           "exact"
           (Term.app `not_first_countable_topology_alexandroff [`inferInstance]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `not_first_countable_topology_alexandroff [`inferInstance]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_first_countable_topology_alexandroff [`inferInstance])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_first_countable_topology_alexandroff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term¬_»
       "¬"
       (Term.app `SecondCountableTopology [(Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `SecondCountableTopology [(Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Instances.RatLemmas.«termℚ∞»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Instances.RatLemmas.«termℚ∞»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.Instances.RatLemmas.«termℚ∞» "ℚ∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Instances.RatLemmas.«termℚ∞»', expected 'Topology.Instances.RatLemmas.termℚ∞._@.Topology.Instances.RatLemmas._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  not_second_countable_topology_alexandroff
  : ¬ SecondCountableTopology ℚ∞
  := by intro exact not_first_countable_topology_alexandroff inferInstance
#align rat.not_second_countable_topology_alexandroff Rat.not_second_countable_topology_alexandroff

instance : TotallyDisconnectedSpace ℚ :=
  by
  refine' ⟨fun s hsu hs x hx y hy => _⟩; clear hsu
  by_contra' H : x ≠ y
  wlog hlt : x < y := H.lt_or_lt using x y, y x
  rcases exists_irrational_btwn (Rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩
  have := hs.image coe continuous_coe_real.continuous_on
  rw [is_preconnected_iff_ord_connected] at this
  have : z ∈ coe '' s := this.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨hxz.le, hzy.le⟩
  exact hz (image_subset_range _ _ this)

end Rat

