/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.kuratowski
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.LpSpace
import Mathbin.Topology.Sets.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℝ)`.
-/


noncomputable section

open Set Metric TopologicalSpace

open Ennreal

-- mathport name: exprℓ_infty_ℝ
local notation "ℓ_infty_ℝ" => lp (fun n : ℕ => ℝ) ∞

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace kuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℝ) -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder
       "{"
       [`f `g]
       [":" (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")]
       "}")
      (Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
      (Term.implicitBinder "{" [`C] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
      (Term.instBinder "[" [] (Term.app `MetricSpace [`α]) "]")
      (Term.explicitBinder "(" [`x] [":" (Term.arrow (termℕ "ℕ") "→" `α)] [] ")")
      (Term.explicitBinder "(" [`a `b] [":" `α] [] ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (termℕ "ℕ") "→" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `MetricSpace [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MetricSpace
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ', expected 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ._@.Topology.MetricSpace.Kuratowski._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable { f g : ℓ_infty_ℝ } { n : ℕ } { C : ℝ } [ MetricSpace α ] ( x : ℕ → α ) ( a b : α )

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A metric space can be embedded in `l^∞(ℝ)` via the distances to points in\na fixed countable set, if this set is dense. This map is given in `Kuratowski_embedding`,\nwithout density assumptions. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `embeddingOfSubset [])
      (Command.optDeclSig
       []
       [(Term.typeSpec ":" (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ"))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           («term_-_»
            (Term.app `dist [`a (Term.app `x [`n])])
            "-"
            (Term.app `dist [(Term.app `x [(num "0")]) (Term.app `x [`n])]))))
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.apply "apply" `mem_ℓp_infty)
             []
             (Mathlib.Tactic.«tacticUse_,,» "use" [(Term.app `dist [`a (Term.app `x [(num "0")])])])
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app `abs_dist_sub_le [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])))]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          («term_-_»
           (Term.app `dist [`a (Term.app `x [`n])])
           "-"
           (Term.app `dist [(Term.app `x [(num "0")]) (Term.app `x [`n])]))))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.apply "apply" `mem_ℓp_infty)
            []
            (Mathlib.Tactic.«tacticUse_,,» "use" [(Term.app `dist [`a (Term.app `x [(num "0")])])])
            []
            (Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app `abs_dist_sub_le [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply "apply" `mem_ℓp_infty)
          []
          (Mathlib.Tactic.«tacticUse_,,» "use" [(Term.app `dist [`a (Term.app `x [(num "0")])])])
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `abs_dist_sub_le [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `abs_dist_sub_le [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_dist_sub_le [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `abs_dist_sub_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.clear "-"))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `n)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.«tacticUse_,,» "use" [(Term.app `dist [`a (Term.app `x [(num "0")])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [`a (Term.app `x [(num "0")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `x [(num "0")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `mem_ℓp_infty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_ℓp_infty
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        («term_-_»
         (Term.app `dist [`a (Term.app `x [`n])])
         "-"
         (Term.app `dist [(Term.app `x [(num "0")]) (Term.app `x [`n])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app `dist [`a (Term.app `x [`n])])
       "-"
       (Term.app `dist [(Term.app `x [(num "0")]) (Term.app `x [`n])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dist [(Term.app `x [(num "0")]) (Term.app `x [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `x [`n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `x [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `x [(num "0")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `dist [`a (Term.app `x [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `x [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `x [`n]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ', expected 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ._@.Topology.MetricSpace.Kuratowski._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
    a fixed countable set, if this set is dense. This map is given in `Kuratowski_embedding`,
    without density assumptions. -/
  def
    embeddingOfSubset
    : ℓ_infty_ℝ
    :=
      ⟨
        fun n => dist a x n - dist x 0 x n
          ,
          by apply mem_ℓp_infty use dist a x 0 rintro - ⟨ n , rfl ⟩ exact abs_dist_sub_le _ _ _
        ⟩
#align Kuratowski_embedding.embedding_of_subset KuratowskiEmbedding.embeddingOfSubset

theorem embedding_of_subset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl
#align Kuratowski_embedding.embedding_of_subset_coe KuratowskiEmbedding.embedding_of_subset_coe

/-- The embedding map is always a semi-contraction. -/
theorem embedding_of_subset_dist_le (a b : α) :
    dist (embeddingOfSubset x a) (embeddingOfSubset x b) ≤ dist a b :=
  by
  refine' lp.norm_le_of_forall_le dist_nonneg fun n => _
  simp only [lp.coe_fn_sub, Pi.sub_apply, embedding_of_subset_coe, Real.dist_eq]
  convert abs_dist_sub_le a b (x n) using 2
  ring
#align
  Kuratowski_embedding.embedding_of_subset_dist_le KuratowskiEmbedding.embedding_of_subset_dist_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[["[", expr add_le_add_left, ",", expr le_abs_self, "]"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[["[", expr add_le_add, ",", expr mul_le_mul_of_nonneg_left, ",", expr hn.le, ",", expr le_refl, "]"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error -/
/-- When the reference set is dense, the embedding map is an isometry on its image. -/
theorem embedding_of_subset_isometry (H : DenseRange x) : Isometry (embeddingOfSubset x) :=
  by
  refine' Isometry.of_dist_eq fun a b => _
  refine' (embedding_of_subset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => _)
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- Second step: use the norm control at index n to conclude
  have C : dist b (x n) - dist a (x n) = embedding_of_subset x b n - embedding_of_subset x a n := by
    simp only [embedding_of_subset_coe, sub_sub_sub_cancel_right]
  have :=
    calc
      dist a b ≤ dist a (x n) + dist (x n) b := dist_triangle _ _ _
      _ = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) :=
        by
        simp [dist_comm]
        ring
      _ ≤ 2 * dist a (x n) + |dist b (x n) - dist a (x n)| := by
        trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\"[\", expr add_le_add_left, \",\", expr le_abs_self, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error"
      _ ≤ 2 * (e / 2) + |embedding_of_subset x b n - embedding_of_subset x a n| := by rw [C];
        trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\"[\", expr add_le_add, \",\", expr mul_le_mul_of_nonneg_left, \",\", expr hn.le, \",\", expr le_refl, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error";
        norm_num
      _ ≤ 2 * (e / 2) + dist (embedding_of_subset x b) (embedding_of_subset x a) :=
        by
        have :
          |embedding_of_subset x b n - embedding_of_subset x a n| ≤
            dist (embedding_of_subset x b) (embedding_of_subset x a) :=
          by
          simpa [dist_eq_norm] using
            lp.norm_apply_le_norm Ennreal.top_ne_zero
              (embedding_of_subset x b - embedding_of_subset x a) n
        nlinarith
      _ = dist (embedding_of_subset x b) (embedding_of_subset x a) + e := by ring
      
  simpa [dist_comm] using this
#align
  Kuratowski_embedding.embedding_of_subset_isometry KuratowskiEmbedding.embedding_of_subset_isometry

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Every separable metric space embeds isometrically in `ℓ_infty_ℝ`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_isometric_embedding [])
      (Command.declSig
       [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [`u])] [] ")")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`α]) "]")
        (Term.instBinder "[" [] (Term.app `SeparableSpace [`α]) "]")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `f)]
           [":" (Term.arrow `α "→" (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
         ","
         (Term.app `Isometry [`f]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.cases'
            "cases'"
            [(Tactic.casesTarget
              []
              (Term.proj
               (Term.typeAscription "(" `univ ":" [(Term.app `Set [`α])] ")")
               "."
               `eq_empty_or_nonempty))]
            []
            ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.«tacticUse_,,»
              "use"
              [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (num "0")))])
             []
             (Tactic.intro "intro" [`x])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `absurd
               [`h
                (Term.app
                 `nonempty.ne_empty
                 [(Term.anonymousCtor "⟨" [`x "," (Term.app `mem_univ [`x])] "⟩")])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `h)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `basepoint)])
                     [])]
                   "⟩")])
                [])])
             []
             (Std.Tactic.tacticHaveI_
              "haveI"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `Inhabited [`α]))]
                ":="
                (Term.anonymousCtor "⟨" [`basepoint] "⟩"))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders
                     [(Lean.binderIdent `s)]
                     [":" (Term.app `Set [`α])]))
                   ","
                   («term_∧_» (Term.proj `s "." `Countable) "∧" (Term.app `Dense [`s]))))]
                ":="
                (Term.app `exists_countable_dense [`α]))))
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `this)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `S_countable)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `S_dense)])
                          [])]
                        "⟩")])
                     [])]
                   "⟩")])
                [])])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj `Set.countable_iff_exists_subset_range "." (fieldIdx "1"))
                 [`S_countable]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x_range)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `embedding_of_subset [`x])
                ","
                (Term.app `embedding_of_subset_isometry [`x (Term.app `S_dense.mono [`x_range])])]
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
         [(Tactic.cases'
           "cases'"
           [(Tactic.casesTarget
             []
             (Term.proj
              (Term.typeAscription "(" `univ ":" [(Term.app `Set [`α])] ")")
              "."
              `eq_empty_or_nonempty))]
           []
           ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.«tacticUse_,,»
             "use"
             [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (num "0")))])
            []
            (Tactic.intro "intro" [`x])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `absurd
              [`h
               (Term.app
                `nonempty.ne_empty
                [(Term.anonymousCtor "⟨" [`x "," (Term.app `mem_univ [`x])] "⟩")])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `h)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `basepoint)])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.tacticHaveI_
             "haveI"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" (Term.app `Inhabited [`α]))]
               ":="
               (Term.anonymousCtor "⟨" [`basepoint] "⟩"))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term∃_,_»
                  "∃"
                  (Lean.explicitBinders
                   (Lean.unbracketedExplicitBinders
                    [(Lean.binderIdent `s)]
                    [":" (Term.app `Set [`α])]))
                  ","
                  («term_∧_» (Term.proj `s "." `Countable) "∧" (Term.app `Dense [`s]))))]
               ":="
               (Term.app `exists_countable_dense [`α]))))
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `this)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `S_countable)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `S_dense)])
                         [])]
                       "⟩")])
                    [])]
                  "⟩")])
               [])])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj `Set.countable_iff_exists_subset_range "." (fieldIdx "1"))
                [`S_countable]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x_range)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `embedding_of_subset [`x])
               ","
               (Term.app `embedding_of_subset_isometry [`x (Term.app `S_dense.mono [`x_range])])]
              "⟩"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `h)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `basepoint)])
                [])]
              "⟩")])
           [])])
        []
        (Std.Tactic.tacticHaveI_
         "haveI"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" (Term.app `Inhabited [`α]))]
           ":="
           (Term.anonymousCtor "⟨" [`basepoint] "⟩"))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Set [`α])]))
              ","
              («term_∧_» (Term.proj `s "." `Countable) "∧" (Term.app `Dense [`s]))))]
           ":="
           (Term.app `exists_countable_dense [`α]))))
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `this)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.one `S_countable)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S_dense)])
                     [])]
                   "⟩")])
                [])]
              "⟩")])
           [])])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            (Term.proj `Set.countable_iff_exists_subset_range "." (fieldIdx "1"))
            [`S_countable]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x_range)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `embedding_of_subset [`x])
           ","
           (Term.app `embedding_of_subset_isometry [`x (Term.app `S_dense.mono [`x_range])])]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `embedding_of_subset [`x])
         ","
         (Term.app `embedding_of_subset_isometry [`x (Term.app `S_dense.mono [`x_range])])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `embedding_of_subset [`x])
        ","
        (Term.app `embedding_of_subset_isometry [`x (Term.app `S_dense.mono [`x_range])])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `embedding_of_subset_isometry [`x (Term.app `S_dense.mono [`x_range])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `S_dense.mono [`x_range])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x_range
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `S_dense.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `S_dense.mono [`x_range]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `embedding_of_subset_isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `embedding_of_subset [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `embedding_of_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          (Term.proj `Set.countable_iff_exists_subset_range "." (fieldIdx "1"))
          [`S_countable]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x_range)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Set.countable_iff_exists_subset_range "." (fieldIdx "1"))
       [`S_countable])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S_countable
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Set.countable_iff_exists_subset_range "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Set.countable_iff_exists_subset_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `this)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S_countable)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S_dense)])
                   [])]
                 "⟩")])
              [])]
            "⟩")])
         [])])
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
           («term∃_,_»
            "∃"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Set [`α])]))
            ","
            («term_∧_» (Term.proj `s "." `Countable) "∧" (Term.app `Dense [`s]))))]
         ":="
         (Term.app `exists_countable_dense [`α]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exists_countable_dense [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_countable_dense
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Set [`α])]))
       ","
       («term_∧_» (Term.proj `s "." `Countable) "∧" (Term.app `Dense [`s])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_» (Term.proj `s "." `Countable) "∧" (Term.app `Dense [`s]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Dense [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Dense
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.proj `s "." `Countable)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" (Term.app `Inhabited [`α]))]
         ":="
         (Term.anonymousCtor "⟨" [`basepoint] "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`basepoint] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `basepoint
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Inhabited [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Inhabited
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `h)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `basepoint)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.«tacticUse_,,»
         "use"
         [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (num "0")))])
        []
        (Tactic.intro "intro" [`x])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `absurd
          [`h
           (Term.app
            `nonempty.ne_empty
            [(Term.anonymousCtor "⟨" [`x "," (Term.app `mem_univ [`x])] "⟩")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `absurd
        [`h
         (Term.app
          `nonempty.ne_empty
          [(Term.anonymousCtor "⟨" [`x "," (Term.app `mem_univ [`x])] "⟩")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `absurd
       [`h
        (Term.app
         `nonempty.ne_empty
         [(Term.anonymousCtor "⟨" [`x "," (Term.app `mem_univ [`x])] "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `nonempty.ne_empty
       [(Term.anonymousCtor "⟨" [`x "," (Term.app `mem_univ [`x])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`x "," (Term.app `mem_univ [`x])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_univ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_univ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nonempty.ne_empty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `nonempty.ne_empty [(Term.anonymousCtor "⟨" [`x "," (Term.app `mem_univ [`x])] "⟩")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `absurd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.«tacticUse_,,»
       "use"
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (num "0")))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget
         []
         (Term.proj
          (Term.typeAscription "(" `univ ":" [(Term.app `Set [`α])] ")")
          "."
          `eq_empty_or_nonempty))]
       []
       ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription "(" `univ ":" [(Term.app `Set [`α])] ")")
       "."
       `eq_empty_or_nonempty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `univ ":" [(Term.app `Set [`α])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `f)]
         [":" (Term.arrow `α "→" (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ"))]))
       ","
       (Term.app `Isometry [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Isometry [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `α "→" (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ', expected 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ._@.Topology.MetricSpace.Kuratowski._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Every separable metric space embeds isometrically in `ℓ_infty_ℝ`. -/
  theorem
    exists_isometric_embedding
    ( α : Type u ) [ MetricSpace α ] [ SeparableSpace α ] : ∃ f : α → ℓ_infty_ℝ , Isometry f
    :=
      by
        cases' ( univ : Set α ) . eq_empty_or_nonempty with h h
          · use fun _ => 0 intro x exact absurd h nonempty.ne_empty ⟨ x , mem_univ x ⟩
          ·
            rcases h with ⟨ basepoint ⟩
              haveI : Inhabited α := ⟨ basepoint ⟩
              have : ∃ s : Set α , s . Countable ∧ Dense s := exists_countable_dense α
              rcases this with ⟨ S , ⟨ S_countable , S_dense ⟩ ⟩
              rcases Set.countable_iff_exists_subset_range . 1 S_countable with ⟨ x , x_range ⟩
              exact ⟨ embedding_of_subset x , embedding_of_subset_isometry x S_dense.mono x_range ⟩
#align
  Kuratowski_embedding.exists_isometric_embedding KuratowskiEmbedding.exists_isometric_embedding

end kuratowskiEmbedding

open TopologicalSpace kuratowskiEmbedding

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℝ)`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `kuratowskiEmbedding [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [`u])] [] ")")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`α]) "]")
        (Term.instBinder "[" [] (Term.app `SeparableSpace [`α]) "]")]
       [(Term.typeSpec
         ":"
         (Term.arrow `α "→" (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")))])
      (Command.declValSimple
       ":="
       (Term.app
        `Classical.choose
        [(Term.app `KuratowskiEmbedding.exists_isometric_embedding [`α])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Classical.choose [(Term.app `KuratowskiEmbedding.exists_isometric_embedding [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `KuratowskiEmbedding.exists_isometric_embedding [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `KuratowskiEmbedding.exists_isometric_embedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `KuratowskiEmbedding.exists_isometric_embedding [`α])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.choose
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow `α "→" (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ', expected 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ._@.Topology.MetricSpace.Kuratowski._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℝ)`. -/
  def
    kuratowskiEmbedding
    ( α : Type u ) [ MetricSpace α ] [ SeparableSpace α ] : α → ℓ_infty_ℝ
    := Classical.choose KuratowskiEmbedding.exists_isometric_embedding α
#align Kuratowski_embedding kuratowskiEmbedding

/-- The Kuratowski embedding is an isometry. -/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.choose_spec (exists_isometric_embedding α)
#align Kuratowski_embedding.isometry kuratowskiEmbedding.isometry

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Version of the Kuratowski embedding for nonempty compacts -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `NonemptyCompacts.kuratowskiEmbedding [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`α] [":" (Term.type "Type" [`u])] [] ")")
        (Term.instBinder "[" [] (Term.app `MetricSpace [`α]) "]")
        (Term.instBinder "[" [] (Term.app `CompactSpace [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Nonempty [`α]) "]")]
       [(Term.typeSpec
         ":"
         (Term.app
          `NonemptyCompacts
          [(Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `carrier
           []
           []
           ":="
           (Term.app `range [(Term.app `kuratowskiEmbedding [`α])]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `is_compact'
           []
           []
           ":="
           (Term.app
            `is_compact_range
            [(Term.proj (Term.app `kuratowskiEmbedding.isometry [`α]) "." `Continuous)]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl `nonempty' [] [] ":=" (Term.app `range_nonempty [(Term.hole "_")]))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range_nonempty [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range_nonempty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_compact_range
       [(Term.proj (Term.app `kuratowskiEmbedding.isometry [`α]) "." `Continuous)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `kuratowskiEmbedding.isometry [`α]) "." `Continuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `kuratowskiEmbedding.isometry [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding.isometry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `kuratowskiEmbedding.isometry [`α])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `range [(Term.app `kuratowskiEmbedding [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `kuratowskiEmbedding [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `kuratowskiEmbedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `kuratowskiEmbedding [`α])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `NonemptyCompacts [(Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ "ℓ_infty_ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ', expected 'Topology.MetricSpace.Kuratowski.termℓ_infty_ℝ._@.Topology.MetricSpace.Kuratowski._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Version of the Kuratowski embedding for nonempty compacts -/
  def
    NonemptyCompacts.kuratowskiEmbedding
    ( α : Type u ) [ MetricSpace α ] [ CompactSpace α ] [ Nonempty α ] : NonemptyCompacts ℓ_infty_ℝ
    where
      carrier := range kuratowskiEmbedding α
        is_compact' := is_compact_range kuratowskiEmbedding.isometry α . Continuous
        nonempty' := range_nonempty _
#align nonempty_compacts.Kuratowski_embedding NonemptyCompacts.kuratowskiEmbedding

