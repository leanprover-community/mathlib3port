/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.simple_graph.regularity.bound
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Order.Partition.Equipartition

/-!
# Numerical bounds for Szemerédi Regularity Lemma

This file gathers the numerical facts required by the proof of Szemerédi's regularity lemma.

## Main declarations

* `szemeredi_regularity.step_bound`: During the inductive step, a partition of size `n` is blown to
  size at most `step_bound n`.
* `szemeredi_regularity.initial_bound`: The size of the partition we start the induction with.
* `szemeredi_regularity.bound`: The upper bound on the size of the partition produced by our version
  of Szemerédi's regularity lemma.
-/


open Finset Fintype Function Real

namespace SzemerediRegularity

/-- Auxiliary function for Szemerédi's regularity lemma. Blowing up a partition of size `n` during
the induction results in a partition of size at most `step_bound n`. -/
def stepBound (n : ℕ) : ℕ :=
  n * 4 ^ n
#align szemeredi_regularity.step_bound SzemerediRegularity.stepBound

theorem le_step_bound : id ≤ step_bound := fun n =>
  Nat.le_mul_of_pos_right <| pow_pos (by norm_num) n
#align szemeredi_regularity.le_step_bound SzemerediRegularity.le_step_bound

theorem step_bound_mono : Monotone stepBound := fun a b h =>
  Nat.mul_le_mul h <| Nat.pow_le_pow_of_le_right (by norm_num) h
#align szemeredi_regularity.step_bound_mono SzemerediRegularity.step_bound_mono

theorem step_bound_pos_iff {n : ℕ} : 0 < stepBound n ↔ 0 < n :=
  zero_lt_mul_right <| by positivity
#align szemeredi_regularity.step_bound_pos_iff SzemerediRegularity.step_bound_pos_iff

alias step_bound_pos_iff ↔ _ step_bound_pos

variable {α : Type _} [DecidableEq α] [Fintype α] {P : Finpartition (univ : Finset α)}
  {u : Finset α} {ε : ℝ}

-- mathport name: exprm
local notation "m" => (card α / stepBound P.parts.card : ℕ)

-- mathport name: expra
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.notation
     []
     []
     (Term.attrKind [(Term.local "local")])
     "notation"
     []
     []
     []
     [(str "\"a\"")]
     "=>"
     (Term.typeAscription
      "("
      («term_-_»
       («term_/_» (Term.app `card [`α]) "/" (Term.proj (Term.proj `P "." `parts) "." `card))
       "-"
       («term_*_»
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
        "*"
        («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))))
      ":"
      [(termℕ "ℕ")]
      ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_-_»
        («term_/_» (Term.app `card [`α]) "/" (Term.proj (Term.proj `P "." `parts) "." `card))
        "-"
        («term_*_»
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
         "*"
         («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))))
       ":"
       [(termℕ "ℕ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       («term_/_» (Term.app `card [`α]) "/" (Term.proj (Term.proj `P "." `parts) "." `card))
       "-"
       («term_*_»
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
        "*"
        («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
       "*"
       («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `P "." `parts) "." `card)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `P "." `parts)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'-/-- failed to format: format: uncaught backtrack exception
local notation "a" => ( card α / P . parts . card - m * 4 ^ P . parts . card : ℕ )

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `m_pos [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nonempty [`α]) "]")
        (Term.explicitBinder
         "("
         [`hPα]
         [":"
          («term_≤_»
           («term_*_»
            (Term.proj (Term.proj `P "." `parts) "." `card)
            "*"
            («term_^_» (num "16") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
           "≤"
           (Term.app `card [`α]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         (num "0")
         "<"
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app
         `Nat.div_pos
         [(Term.app
           (Term.proj
            («term_<|_»
             (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
             "<|"
             (Term.app
              `Nat.pow_le_pow_of_le_left
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
               (Term.hole "_")]))
            "."
            `trans)
           [`hPα])])
        "<|"
        (Term.app
         `step_bound_pos
         [(Term.proj
           («term_<|_»
            (Term.proj `P "." `parts_nonempty)
            "<|"
            (Term.proj `univ_nonempty "." `ne_empty))
           "."
           `card_pos)]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app
        `Nat.div_pos
        [(Term.app
          (Term.proj
           («term_<|_»
            (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
            "<|"
            (Term.app
             `Nat.pow_le_pow_of_le_left
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
              (Term.hole "_")]))
           "."
           `trans)
          [`hPα])])
       "<|"
       (Term.app
        `step_bound_pos
        [(Term.proj
          («term_<|_»
           (Term.proj `P "." `parts_nonempty)
           "<|"
           (Term.proj `univ_nonempty "." `ne_empty))
          "."
          `card_pos)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `step_bound_pos
       [(Term.proj
         («term_<|_»
          (Term.proj `P "." `parts_nonempty)
          "<|"
          (Term.proj `univ_nonempty "." `ne_empty))
         "."
         `card_pos)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       («term_<|_» (Term.proj `P "." `parts_nonempty) "<|" (Term.proj `univ_nonempty "." `ne_empty))
       "."
       `card_pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» (Term.proj `P "." `parts_nonempty) "<|" (Term.proj `univ_nonempty "." `ne_empty))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `univ_nonempty "." `ne_empty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `univ_nonempty
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `P "." `parts_nonempty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.proj `P "." `parts_nonempty) "<|" (Term.proj `univ_nonempty "." `ne_empty))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `step_bound_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app
       `Nat.div_pos
       [(Term.app
         (Term.proj
          («term_<|_»
           (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
           "<|"
           (Term.app
            `Nat.pow_le_pow_of_le_left
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
             (Term.hole "_")]))
          "."
          `trans)
         [`hPα])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        («term_<|_»
         (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
         "<|"
         (Term.app
          `Nat.pow_le_pow_of_le_left
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
           (Term.hole "_")]))
        "."
        `trans)
       [`hPα])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPα
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       («term_<|_»
        (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
        "<|"
        (Term.app
         `Nat.pow_le_pow_of_le_left
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
          (Term.hole "_")]))
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
       "<|"
       (Term.app
        `Nat.pow_le_pow_of_le_left
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Nat.pow_le_pow_of_le_left
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.pow_le_pow_of_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.mul_le_mul_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
      "<|"
      (Term.app
       `Nat.pow_le_pow_of_le_left
       [(Term.paren
         "("
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
         ")")
        (Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren
        "("
        («term_<|_»
         (Term.app `Nat.mul_le_mul_left [(Term.hole "_")])
         "<|"
         (Term.app
          `Nat.pow_le_pow_of_le_left
          [(Term.paren
            "("
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
            ")")
           (Term.hole "_")]))
        ")")
       "."
       `trans)
      [`hPα])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.div_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       (num "0")
       "<"
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  m_pos
  [ Nonempty α ] ( hPα : P . parts . card * 16 ^ P . parts . card ≤ card α ) : 0 < m
  :=
    Nat.div_pos Nat.mul_le_mul_left _ <| Nat.pow_le_pow_of_le_left by norm_num _ . trans hPα
      <|
      step_bound_pos P . parts_nonempty <| univ_nonempty . ne_empty . card_pos
#align szemeredi_regularity.m_pos SzemerediRegularity.m_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `m_coe_pos [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nonempty [`α]) "]")
        (Term.explicitBinder
         "("
         [`hPα]
         [":"
          («term_≤_»
           («term_*_»
            (Term.proj (Term.proj `P "." `parts) "." `card)
            "*"
            («term_^_» (num "16") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
           "≤"
           (Term.app `card [`α]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         "<"
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))))
      (Command.declValSimple
       ":="
       («term_<|_» (Term.proj `Nat.cast_pos "." (fieldIdx "2")) "<|" (Term.app `m_pos [`hPα]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» (Term.proj `Nat.cast_pos "." (fieldIdx "2")) "<|" (Term.app `m_pos [`hPα]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `m_pos [`hPα])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPα
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `m_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `Nat.cast_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Nat.cast_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       "<"
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  m_coe_pos
  [ Nonempty α ] ( hPα : P . parts . card * 16 ^ P . parts . card ≤ card α ) : ( 0 : ℝ ) < m
  := Nat.cast_pos . 2 <| m_pos hPα
#align szemeredi_regularity.m_coe_pos SzemerediRegularity.m_coe_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_m_add_one_pos [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_<_»
         (num "0")
         "<"
         («term_+_»
          (Term.typeAscription
           "("
           (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
           ":"
           [(Data.Real.Basic.termℝ "ℝ")]
           ")")
          "+"
          (num "1")))))
      (Command.declValSimple ":=" (Term.app `Nat.cast_add_one_pos [(Term.hole "_")]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.cast_add_one_pos [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.cast_add_one_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       (num "0")
       "<"
       («term_+_»
        (Term.typeAscription
         "("
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        "+"
        (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.typeAscription
        "("
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")")
       "+"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.typeAscription
       "("
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem coe_m_add_one_pos : 0 < ( m : ℝ ) + 1 := Nat.cast_add_one_pos _
#align szemeredi_regularity.coe_m_add_one_pos SzemerediRegularity.coe_m_add_one_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `one_le_m_coe [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nonempty [`α]) "]")
        (Term.explicitBinder
         "("
         [`hPα]
         [":"
          («term_≤_»
           («term_*_»
            (Term.proj (Term.proj `P "." `parts) "." `card)
            "*"
            («term_^_» (num "16") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
           "≤"
           (Term.app `card [`α]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         "≤"
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))))
      (Command.declValSimple
       ":="
       («term_<|_» (Term.proj `Nat.one_le_cast "." (fieldIdx "2")) "<|" (Term.app `m_pos [`hPα]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» (Term.proj `Nat.one_le_cast "." (fieldIdx "2")) "<|" (Term.app `m_pos [`hPα]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `m_pos [`hPα])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPα
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `m_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `Nat.one_le_cast "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Nat.one_le_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       "≤"
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  one_le_m_coe
  [ Nonempty α ] ( hPα : P . parts . card * 16 ^ P . parts . card ≤ card α ) : ( 1 : ℝ ) ≤ m
  := Nat.one_le_cast . 2 <| m_pos hPα
#align szemeredi_regularity.one_le_m_coe SzemerediRegularity.one_le_m_coe

theorem eps_pow_five_pos (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) : 0 < ε ^ 5 :=
  pos_of_mul_pos_right ((by norm_num : (0 : ℝ) < 100).trans_le hPε) <| pow_nonneg (by norm_num) _
#align szemeredi_regularity.eps_pow_five_pos SzemerediRegularity.eps_pow_five_pos

theorem eps_pos (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) : 0 < ε :=
  pow_bit1_pos_iff.1 <| eps_pow_five_pos hPε
#align szemeredi_regularity.eps_pos SzemerediRegularity.eps_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `hundred_div_ε_pow_five_le_m [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nonempty [`α]) "]")
        (Term.explicitBinder
         "("
         [`hPα]
         [":"
          («term_≤_»
           («term_*_»
            (Term.proj (Term.proj `P "." `parts) "." `card)
            "*"
            («term_^_» (num "16") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
           "≤"
           (Term.app `card [`α]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hPε]
         [":"
          («term_≤_»
           (num "100")
           "≤"
           («term_*_»
            («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))
            "*"
            («term_^_» `ε "^" (num "5"))))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         («term_/_» (num "100") "/" («term_^_» `ε "^" (num "5")))
         "≤"
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (Term.app
          `div_le_of_nonneg_of_le_mul
          [(Term.proj (Term.app `eps_pow_five_pos [`hPε]) "." `le)
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
           `hPε])
         "."
         `trans)
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
             []
             (Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  `Nat.le_div_iff_mul_le'
                  [(Term.app
                    `step_bound_pos
                    [(Term.proj
                      («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty)
                      "."
                      `card_pos)])]))
                ","
                (Tactic.rwRule [] `step_bound)
                ","
                (Tactic.rwRule [] `mul_left_comm)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)]
               "]")
              [])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `div_le_of_nonneg_of_le_mul
         [(Term.proj (Term.app `eps_pow_five_pos [`hPε]) "." `le)
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
          `hPε])
        "."
        `trans)
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `Nat.le_div_iff_mul_le'
                 [(Term.app
                   `step_bound_pos
                   [(Term.proj
                     («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty)
                     "."
                     `card_pos)])]))
               ","
               (Tactic.rwRule [] `step_bound)
               ","
               (Tactic.rwRule [] `mul_left_comm)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)]
              "]")
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `Nat.le_div_iff_mul_le'
               [(Term.app
                 `step_bound_pos
                 [(Term.proj
                   («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty)
                   "."
                   `card_pos)])]))
             ","
             (Tactic.rwRule [] `step_bound)
             ","
             (Tactic.rwRule [] `mul_left_comm)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `Nat.le_div_iff_mul_le'
           [(Term.app
             `step_bound_pos
             [(Term.proj
               («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty)
               "."
               `card_pos)])]))
         ","
         (Tactic.rwRule [] `step_bound)
         ","
         (Tactic.rwRule [] `mul_left_comm)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_left_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `step_bound
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Nat.le_div_iff_mul_le'
       [(Term.app
         `step_bound_pos
         [(Term.proj («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty) "." `card_pos)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `step_bound_pos
       [(Term.proj («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty) "." `card_pos)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty) "." `card_pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `univ_nonempty.ne_empty
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `P.parts_nonempty
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `step_bound_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `step_bound_pos
      [(Term.proj
        (Term.paren "(" («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty) ")")
        "."
        `card_pos)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.le_div_iff_mul_le'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
         []
         (Std.Tactic.tacticRwa__
          "rwa"
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule
             []
             (Term.app
              `Nat.le_div_iff_mul_le'
              [(Term.paren
                "("
                (Term.app
                 `step_bound_pos
                 [(Term.proj
                   (Term.paren "(" («term_<|_» `P.parts_nonempty "<|" `univ_nonempty.ne_empty) ")")
                   "."
                   `card_pos)])
                ")")]))
            ","
            (Tactic.rwRule [] `step_bound)
            ","
            (Tactic.rwRule [] `mul_left_comm)
            ","
            (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_pow)]
           "]")
          [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `div_le_of_nonneg_of_le_mul
        [(Term.proj (Term.app `eps_pow_five_pos [`hPε]) "." `le)
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
         `hPε])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `div_le_of_nonneg_of_le_mul
       [(Term.proj (Term.app `eps_pow_five_pos [`hPε]) "." `le)
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
        `hPε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Positivity.positivity "positivity")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `eps_pow_five_pos [`hPε]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `eps_pow_five_pos [`hPε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eps_pow_five_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `eps_pow_five_pos [`hPε]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_of_nonneg_of_le_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `div_le_of_nonneg_of_le_mul
      [(Term.proj (Term.paren "(" (Term.app `eps_pow_five_pos [`hPε]) ")") "." `le)
       (Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.Positivity.positivity "positivity")])))
        ")")
       `hPε])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       («term_/_» (num "100") "/" («term_^_» `ε "^" (num "5")))
       "≤"
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  hundred_div_ε_pow_five_le_m
  [ Nonempty α ]
      ( hPα : P . parts . card * 16 ^ P . parts . card ≤ card α )
      ( hPε : 100 ≤ 4 ^ P . parts . card * ε ^ 5 )
    : 100 / ε ^ 5 ≤ m
  :=
    div_le_of_nonneg_of_le_mul eps_pow_five_pos hPε . le by positivity hPε . trans
      by
        norm_cast
          rwa
            [
              Nat.le_div_iff_mul_le'
                  step_bound_pos P.parts_nonempty <| univ_nonempty.ne_empty . card_pos
                ,
                step_bound
                ,
                mul_left_comm
                ,
                ← mul_pow
              ]
#align
  szemeredi_regularity.hundred_div_ε_pow_five_le_m SzemerediRegularity.hundred_div_ε_pow_five_le_m

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `hundred_le_m [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nonempty [`α]) "]")
        (Term.explicitBinder
         "("
         [`hPα]
         [":"
          («term_≤_»
           («term_*_»
            (Term.proj (Term.proj `P "." `parts) "." `card)
            "*"
            («term_^_» (num "16") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
           "≤"
           (Term.app `card [`α]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hPε]
         [":"
          («term_≤_»
           (num "100")
           "≤"
           («term_*_»
            («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))
            "*"
            («term_^_» `ε "^" (num "5"))))]
         []
         ")")
        (Term.explicitBinder "(" [`hε] [":" («term_≤_» `ε "≤" (num "1"))] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (num "100")
         "≤"
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.NormCast.tacticExact_mod_cast_
            "exact_mod_cast"
            (Term.app
             (Term.proj
              («term_<|_»
               (Term.app
                `le_div_self
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                 (Term.app `eps_pow_five_pos [`hPε])])
               "<|"
               (Term.app
                `pow_le_one
                [(Term.hole "_") (Term.proj (Term.app `eps_pos [`hPε]) "." `le) `hε]))
              "."
              `trans)
             [(Term.app `hundred_div_ε_pow_five_le_m [`hPα `hPε])]))])))
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
         [(Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           (Term.app
            (Term.proj
             («term_<|_»
              (Term.app
               `le_div_self
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                (Term.app `eps_pow_five_pos [`hPε])])
              "<|"
              (Term.app
               `pow_le_one
               [(Term.hole "_") (Term.proj (Term.app `eps_pos [`hPε]) "." `le) `hε]))
             "."
             `trans)
            [(Term.app `hundred_div_ε_pow_five_le_m [`hPα `hPε])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_
       "exact_mod_cast"
       (Term.app
        (Term.proj
         («term_<|_»
          (Term.app
           `le_div_self
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
            (Term.app `eps_pow_five_pos [`hPε])])
          "<|"
          (Term.app
           `pow_le_one
           [(Term.hole "_") (Term.proj (Term.app `eps_pos [`hPε]) "." `le) `hε]))
         "."
         `trans)
        [(Term.app `hundred_div_ε_pow_five_le_m [`hPα `hPε])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        («term_<|_»
         (Term.app
          `le_div_self
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
           (Term.app `eps_pow_five_pos [`hPε])])
         "<|"
         (Term.app
          `pow_le_one
          [(Term.hole "_") (Term.proj (Term.app `eps_pos [`hPε]) "." `le) `hε]))
        "."
        `trans)
       [(Term.app `hundred_div_ε_pow_five_le_m [`hPα `hPε])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hundred_div_ε_pow_five_le_m [`hPα `hPε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hPα
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hundred_div_ε_pow_five_le_m
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hundred_div_ε_pow_five_le_m [`hPα `hPε])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       («term_<|_»
        (Term.app
         `le_div_self
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
          (Term.app `eps_pow_five_pos [`hPε])])
        "<|"
        (Term.app `pow_le_one [(Term.hole "_") (Term.proj (Term.app `eps_pos [`hPε]) "." `le) `hε]))
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app
        `le_div_self
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
         (Term.app `eps_pow_five_pos [`hPε])])
       "<|"
       (Term.app `pow_le_one [(Term.hole "_") (Term.proj (Term.app `eps_pos [`hPε]) "." `le) `hε]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_le_one [(Term.hole "_") (Term.proj (Term.app `eps_pos [`hPε]) "." `le) `hε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `eps_pos [`hPε]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `eps_pos [`hPε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eps_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `eps_pos [`hPε]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_le_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app
       `le_div_self
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
        (Term.app `eps_pow_five_pos [`hPε])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eps_pow_five_pos [`hPε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eps_pow_five_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `eps_pow_five_pos [`hPε]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_div_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app
       `le_div_self
       [(Term.paren
         "("
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
         ")")
        (Term.paren "(" (Term.app `eps_pow_five_pos [`hPε]) ")")])
      "<|"
      (Term.app
       `pow_le_one
       [(Term.hole "_") (Term.proj (Term.paren "(" (Term.app `eps_pos [`hPε]) ")") "." `le) `hε]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (num "100")
       "≤"
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  hundred_le_m
  [ Nonempty α ]
      ( hPα : P . parts . card * 16 ^ P . parts . card ≤ card α )
      ( hPε : 100 ≤ 4 ^ P . parts . card * ε ^ 5 )
      ( hε : ε ≤ 1 )
    : 100 ≤ m
  :=
    by
      exact_mod_cast
        le_div_self by norm_num eps_pow_five_pos hPε <| pow_le_one _ eps_pos hPε . le hε . trans
          hundred_div_ε_pow_five_le_m hPα hPε
#align szemeredi_regularity.hundred_le_m SzemerediRegularity.hundred_le_m

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `a_add_one_le_four_pow_parts_card [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_≤_»
         («term_+_»
          (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
          "+"
          (num "1"))
         "≤"
         («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))))
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
              [`h []]
              [(Term.typeSpec
                ":"
                («term_≤_» (num "1") "≤" («term_^_» (num "4") "^" `P.parts.card)))]
              ":="
              (Term.app
               `one_le_pow_of_one_le
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                (Term.hole "_")]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `step_bound)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `Nat.le_sub_iff_right [`h]))
              ","
              (Tactic.rwRule [] `tsub_le_iff_left)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.add_sub_assoc [`h]))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app `Nat.le_pred_of_lt [(Term.app `Nat.lt_div_mul_add [`h])]))])))
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
             [`h []]
             [(Term.typeSpec ":" («term_≤_» (num "1") "≤" («term_^_» (num "4") "^" `P.parts.card)))]
             ":="
             (Term.app
              `one_le_pow_of_one_le
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
               (Term.hole "_")]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `step_bound)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `Nat.le_sub_iff_right [`h]))
             ","
             (Tactic.rwRule [] `tsub_le_iff_left)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.add_sub_assoc [`h]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `Nat.le_pred_of_lt [(Term.app `Nat.lt_div_mul_add [`h])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Nat.le_pred_of_lt [(Term.app `Nat.lt_div_mul_add [`h])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.le_pred_of_lt [(Term.app `Nat.lt_div_mul_add [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.lt_div_mul_add [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.lt_div_mul_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Nat.lt_div_mul_add [`h]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.le_pred_of_lt
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
        [(Tactic.rwRule [] `step_bound)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.le_sub_iff_right [`h]))
         ","
         (Tactic.rwRule [] `tsub_le_iff_left)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Nat.add_sub_assoc [`h]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_sub_assoc [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_sub_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tsub_le_iff_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.le_sub_iff_right [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.le_sub_iff_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.div_div_eq_div_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `step_bound
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h []]
         [(Term.typeSpec ":" («term_≤_» (num "1") "≤" («term_^_» (num "4") "^" `P.parts.card)))]
         ":="
         (Term.app
          `one_le_pow_of_one_le
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
           (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `one_le_pow_of_one_le
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_le_pow_of_one_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (num "1") "≤" («term_^_» (num "4") "^" `P.parts.card))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "4") "^" `P.parts.card)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `P.parts.card
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       («term_+_»
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
        "+"
        (num "1"))
       "≤"
       («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `P "." `parts) "." `card)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `P "." `parts)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
       "+"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.54'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  a_add_one_le_four_pow_parts_card
  : a + 1 ≤ 4 ^ P . parts . card
  :=
    by
      have h : 1 ≤ 4 ^ P.parts.card := one_le_pow_of_one_le by norm_num _
        rw
          [
            step_bound
              ,
              ← Nat.div_div_eq_div_mul
              ,
              ← Nat.le_sub_iff_right h
              ,
              tsub_le_iff_left
              ,
              ← Nat.add_sub_assoc h
            ]
        exact Nat.le_pred_of_lt Nat.lt_div_mul_add h
#align
  szemeredi_regularity.a_add_one_le_four_pow_parts_card SzemerediRegularity.a_add_one_le_four_pow_parts_card

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `card_aux₁ [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hucard]
         [":"
          («term_=_»
           (Term.proj `u "." `card)
           "="
           («term_+_»
            («term_*_»
             (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
             "*"
             («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
            "+"
            (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          («term_*_»
           («term_-_»
            («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))
            "-"
            (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a"))
           "*"
           (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
          "+"
          («term_*_»
           (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
           "*"
           («term_+_»
            (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
            "+"
            (num "1"))))
         "="
         (Term.proj `u "." `card))))
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
             [(Tactic.rwRule [] `hucard)
              ","
              (Tactic.rwRule [] `mul_add)
              ","
              (Tactic.rwRule [] `mul_one)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_mul)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `Nat.sub_add_cancel
                [(Term.app
                  (Term.proj (Term.app `Nat.le_succ [(Term.hole "_")]) "." `trans)
                  [`a_add_one_le_four_pow_parts_card])]))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `hucard)
             ","
             (Tactic.rwRule [] `mul_add)
             ","
             (Tactic.rwRule [] `mul_one)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_mul)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `Nat.sub_add_cancel
               [(Term.app
                 (Term.proj (Term.app `Nat.le_succ [(Term.hole "_")]) "." `trans)
                 [`a_add_one_le_four_pow_parts_card])]))
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
        [(Tactic.rwRule [] `hucard)
         ","
         (Tactic.rwRule [] `mul_add)
         ","
         (Tactic.rwRule [] `mul_one)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_mul)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Nat.sub_add_cancel
           [(Term.app
             (Term.proj (Term.app `Nat.le_succ [(Term.hole "_")]) "." `trans)
             [`a_add_one_le_four_pow_parts_card])]))
         ","
         (Tactic.rwRule [] `mul_comm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Nat.sub_add_cancel
       [(Term.app
         (Term.proj (Term.app `Nat.le_succ [(Term.hole "_")]) "." `trans)
         [`a_add_one_le_four_pow_parts_card])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `Nat.le_succ [(Term.hole "_")]) "." `trans)
       [`a_add_one_le_four_pow_parts_card])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_add_one_le_four_pow_parts_card
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Nat.le_succ [(Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Nat.le_succ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.le_succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Nat.le_succ [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `Nat.le_succ [(Term.hole "_")]) ")") "." `trans)
      [`a_add_one_le_four_pow_parts_card])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.sub_add_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hucard
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_+_»
        («term_*_»
         («term_-_»
          («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))
          "-"
          (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a"))
         "*"
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
        "+"
        («term_*_»
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
         "*"
         («term_+_»
          (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
          "+"
          (num "1"))))
       "="
       (Term.proj `u "." `card))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `u "." `card)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       («term_*_»
        («term_-_»
         («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))
         "-"
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a"))
        "*"
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
       "+"
       («term_*_»
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
        "*"
        («term_+_»
         (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
         "+"
         (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
       "*"
       («term_+_»
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
        "+"
        (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
       "+"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  card_aux₁
  ( hucard : u . card = m * 4 ^ P . parts . card + a )
    : 4 ^ P . parts . card - a * m + a * m + 1 = u . card
  :=
    by
      rw
        [
          hucard
            ,
            mul_add
            ,
            mul_one
            ,
            ← add_assoc
            ,
            ← add_mul
            ,
            Nat.sub_add_cancel Nat.le_succ _ . trans a_add_one_le_four_pow_parts_card
            ,
            mul_comm
          ]
#align szemeredi_regularity.card_aux₁ SzemerediRegularity.card_aux₁

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `card_aux₂ [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hP] [":" (Term.proj `P "." `IsEquipartition)] [] ")")
        (Term.explicitBinder "(" [`hu] [":" («term_∈_» `u "∈" (Term.proj `P "." `parts))] [] ")")
        (Term.explicitBinder
         "("
         [`hucard]
         [":"
          («term¬_»
           "¬"
           («term_=_»
            (Term.proj `u "." `card)
            "="
            («term_+_»
             («term_*_»
              (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
              "*"
              («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card)))
             "+"
             (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a"))))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          («term_*_»
           («term_-_»
            («term_^_» (num "4") "^" (Term.proj (Term.proj `P "." `parts) "." `card))
            "-"
            («term_+_»
             (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
             "+"
             (num "1")))
           "*"
           (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
          "+"
          («term_*_»
           («term_+_»
            (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.terma "a")
            "+"
            (num "1"))
           "*"
           («term_+_»
            (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
            "+"
            (num "1"))))
         "="
         (Term.proj `u "." `card))))
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
                («term_≤_»
                 («term_*_»
                  (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
                  "*"
                  («term_^_» (num "4") "^" `P.parts.card))
                 "≤"
                 («term_/_» (Term.app `card [`α]) "/" `P.parts.card)))]
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
                    [(Tactic.rwRule [] `step_bound)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app `Nat.div_mul_le_self [(Term.hole "_") (Term.hole "_")]))]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`this]))] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hucard] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                (Term.proj (Term.app `hP.card_parts_eq_average [`hu]) "." `resolve_left)
                [`hucard]))
              ","
              (Tactic.rwRule [] `mul_add)
              ","
              (Tactic.rwRule [] `mul_one)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_mul)
              ","
              (Tactic.rwRule [] (Term.app `Nat.sub_add_cancel [`a_add_one_le_four_pow_parts_card]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
              ","
              (Tactic.rwRule [] `mul_comm)
              ","
              (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`this]))
              ","
              (Tactic.rwRule [] `card_univ)]
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_≤_»
                («term_*_»
                 (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
                 "*"
                 («term_^_» (num "4") "^" `P.parts.card))
                "≤"
                («term_/_» (Term.app `card [`α]) "/" `P.parts.card)))]
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
                   [(Tactic.rwRule [] `step_bound)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app `Nat.div_mul_le_self [(Term.hole "_") (Term.hole "_")]))]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`this]))] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hucard] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               (Term.proj (Term.app `hP.card_parts_eq_average [`hu]) "." `resolve_left)
               [`hucard]))
             ","
             (Tactic.rwRule [] `mul_add)
             ","
             (Tactic.rwRule [] `mul_one)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_mul)
             ","
             (Tactic.rwRule [] (Term.app `Nat.sub_add_cancel [`a_add_one_le_four_pow_parts_card]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
             ","
             (Tactic.rwRule [] `mul_comm)
             ","
             (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`this]))
             ","
             (Tactic.rwRule [] `card_univ)]
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
          []
          (Term.app
           (Term.proj (Term.app `hP.card_parts_eq_average [`hu]) "." `resolve_left)
           [`hucard]))
         ","
         (Tactic.rwRule [] `mul_add)
         ","
         (Tactic.rwRule [] `mul_one)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_mul)
         ","
         (Tactic.rwRule [] (Term.app `Nat.sub_add_cancel [`a_add_one_le_four_pow_parts_card]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `add_assoc)
         ","
         (Tactic.rwRule [] `mul_comm)
         ","
         (Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`this]))
         ","
         (Tactic.rwRule [] `card_univ)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `card_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_sub_of_le [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_sub_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.sub_add_cancel [`a_add_one_le_four_pow_parts_card])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_add_one_le_four_pow_parts_card
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.sub_add_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `hP.card_parts_eq_average [`hu]) "." `resolve_left) [`hucard])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hucard
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `hP.card_parts_eq_average [`hu]) "." `resolve_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hP.card_parts_eq_average [`hu])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hP.card_parts_eq_average
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hP.card_parts_eq_average [`hu])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Nat.add_sub_of_le [`this]))] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hucard] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hucard
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.add_sub_of_le [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.add_sub_of_le
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
           («term_≤_»
            («term_*_»
             (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
             "*"
             («term_^_» (num "4") "^" `P.parts.card))
            "≤"
            («term_/_» (Term.app `card [`α]) "/" `P.parts.card)))]
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
               [(Tactic.rwRule [] `step_bound)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app `Nat.div_mul_le_self [(Term.hole "_") (Term.hole "_")]))]))))))
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
            [(Tactic.rwRule [] `step_bound)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `Nat.div_mul_le_self [(Term.hole "_") (Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Nat.div_mul_le_self [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.div_mul_le_self [(Term.hole "_") (Term.hole "_")])
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
      `Nat.div_mul_le_self
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
        [(Tactic.rwRule [] `step_bound)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.div_div_eq_div_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `step_bound
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_*_»
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
        "*"
        («term_^_» (num "4") "^" `P.parts.card))
       "≤"
       («term_/_» (Term.app `card [`α]) "/" `P.parts.card))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Term.app `card [`α]) "/" `P.parts.card)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `P.parts.card
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `card [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
       "*"
       («term_^_» (num "4") "^" `P.parts.card))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "4") "^" `P.parts.card)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `P.parts.card
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
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
  card_aux₂
  ( hP : P . IsEquipartition )
      ( hu : u ∈ P . parts )
      ( hucard : ¬ u . card = m * 4 ^ P . parts . card + a )
    : 4 ^ P . parts . card - a + 1 * m + a + 1 * m + 1 = u . card
  :=
    by
      have
          : m * 4 ^ P.parts.card ≤ card α / P.parts.card
            :=
            by rw [ step_bound , ← Nat.div_div_eq_div_mul ] exact Nat.div_mul_le_self _ _
        rw [ Nat.add_sub_of_le this ] at hucard
        rw
          [
            hP.card_parts_eq_average hu . resolve_left hucard
              ,
              mul_add
              ,
              mul_one
              ,
              ← add_assoc
              ,
              ← add_mul
              ,
              Nat.sub_add_cancel a_add_one_le_four_pow_parts_card
              ,
              ← add_assoc
              ,
              mul_comm
              ,
              Nat.add_sub_of_le this
              ,
              card_univ
            ]
#align szemeredi_regularity.card_aux₂ SzemerediRegularity.card_aux₂

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `pow_mul_m_le_card_part [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hP] [":" (Term.proj `P "." `IsEquipartition)] [] ")")
        (Term.explicitBinder "(" [`hu] [":" («term_∈_» `u "∈" (Term.proj `P "." `parts))] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         («term_*_»
          («term_^_»
           (Term.typeAscription "(" (num "4") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
           "^"
           (Term.proj (Term.proj `P "." `parts) "." `card))
          "*"
          (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
         "≤"
         (Term.proj `u "." `card))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `step_bound)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj (Term.app `Nat.mul_div_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
             [(Term.app `hP.average_le_card_part [`hu])]))])))
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
         [(Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `step_bound)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.app `Nat.mul_div_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
            [(Term.app `hP.average_le_card_part [`hu])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `Nat.mul_div_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
        [(Term.app `hP.average_le_card_part [`hu])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `Nat.mul_div_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
       [(Term.app `hP.average_le_card_part [`hu])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hP.average_le_card_part [`hu])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hP.average_le_card_part
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hP.average_le_card_part [`hu])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Nat.mul_div_le [(Term.hole "_") (Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Nat.mul_div_le [(Term.hole "_") (Term.hole "_")])
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
      `Nat.mul_div_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Nat.mul_div_le [(Term.hole "_") (Term.hole "_")])
     ")")
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
        [(Tactic.rwRule [] `step_bound)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.div_div_eq_div_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.div_div_eq_div_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `step_bound
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       («term_*_»
        («term_^_»
         (Term.typeAscription "(" (num "4") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         "^"
         (Term.proj (Term.proj `P "." `parts) "." `card))
        "*"
        (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
       "≤"
       (Term.proj `u "." `card))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `u "." `card)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       («term_^_»
        (Term.typeAscription "(" (num "4") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
        "^"
        (Term.proj (Term.proj `P "." `parts) "." `card))
       "*"
       (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm "m")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm', expected 'SzemerediRegularity.Combinatorics.SimpleGraph.Regularity.Bound.termm._@.Combinatorics.SimpleGraph.Regularity.Bound._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  pow_mul_m_le_card_part
  ( hP : P . IsEquipartition ) ( hu : u ∈ P . parts ) : ( 4 : ℝ ) ^ P . parts . card * m ≤ u . card
  :=
    by
      norm_cast
        rw [ step_bound , ← Nat.div_div_eq_div_mul ]
        exact Nat.mul_div_le _ _ . trans hP.average_le_card_part hu
#align szemeredi_regularity.pow_mul_m_le_card_part SzemerediRegularity.pow_mul_m_le_card_part

variable (P ε) (l : ℕ)

/-- Auxiliary function for Szemerédi's regularity lemma. The size of the partition by which we start
blowing. -/
noncomputable def initialBound : ℕ :=
  max 7 <| max l <| ⌊log (100 / ε ^ 5) / log 4⌋₊ + 1
#align szemeredi_regularity.initial_bound SzemerediRegularity.initialBound

theorem le_initial_bound : l ≤ initialBound ε l :=
  (le_max_left _ _).trans <| le_max_right _ _
#align szemeredi_regularity.le_initial_bound SzemerediRegularity.le_initial_bound

theorem seven_le_initial_bound : 7 ≤ initialBound ε l :=
  le_max_left _ _
#align szemeredi_regularity.seven_le_initial_bound SzemerediRegularity.seven_le_initial_bound

theorem initial_bound_pos : 0 < initialBound ε l :=
  Nat.succ_pos'.trans_le <| seven_le_initial_bound _ _
#align szemeredi_regularity.initial_bound_pos SzemerediRegularity.initial_bound_pos

theorem hundred_lt_pow_initial_bound_mul {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    100 < 4 ^ initialBound ε l * ε ^ 5 :=
  by
  rw [← rpow_nat_cast 4, ← div_lt_iff (pow_pos hε 5), lt_rpow_iff_log_lt _ zero_lt_four, ←
    div_lt_iff, initial_bound, Nat.cast_max, Nat.cast_max]
  · push_cast
    exact lt_max_of_lt_right (lt_max_of_lt_right <| Nat.lt_floor_add_one _)
  · exact log_pos (by norm_num)
  · exact div_pos (by norm_num) (pow_pos hε 5)
#align
  szemeredi_regularity.hundred_lt_pow_initial_bound_mul SzemerediRegularity.hundred_lt_pow_initial_bound_mul

/-- An explicit bound on the size of the equipartition whose existence is given by Szemerédi's
regularity lemma. -/
noncomputable def bound : ℕ :=
  (step_bound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (step_bound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)
#align szemeredi_regularity.bound SzemerediRegularity.bound

theorem initial_bound_le_bound : initialBound ε l ≤ bound ε l :=
  (id_le_iterate_of_id_le le_step_bound _ _).trans <| Nat.le_mul_of_pos_right <| by positivity
#align szemeredi_regularity.initial_bound_le_bound SzemerediRegularity.initial_bound_le_bound

theorem le_bound : l ≤ bound ε l :=
  (le_initial_bound ε l).trans <| initial_bound_le_bound ε l
#align szemeredi_regularity.le_bound SzemerediRegularity.le_bound

theorem bound_pos : 0 < bound ε l :=
  (initial_bound_pos ε l).trans_le <| initial_bound_le_bound ε l
#align szemeredi_regularity.bound_pos SzemerediRegularity.bound_pos

end SzemerediRegularity

namespace Tactic

open Positivity SzemerediRegularity

/-- Extension for the `positivity` tactic: `szemeredi_regularity.initial_bound` and
`szemeredi_regularity.bound` are always positive. -/
@[positivity]
unsafe def positivity_szemeredi_regularity_bound : expr → tactic strictness
  | q(SzemerediRegularity.initialBound $(ε) $(l)) => positive <$> mk_app `` initial_bound_pos [ε, l]
  | q(SzemerediRegularity.bound $(ε) $(l)) => positive <$> mk_app `` bound_pos [ε, l]
  | e =>
    pp e >>=
      fail ∘
        format.bracket "The expression `"
          "` isn't of the form `szemeredi_regularity.initial_bound ε l` nor `szemeredi_regularity.bound ε l`"
#align tactic.positivity_szemeredi_regularity_bound tactic.positivity_szemeredi_regularity_bound

example (ε : ℝ) (l : ℕ) : 0 < SzemerediRegularity.initialBound ε l := by positivity

example (ε : ℝ) (l : ℕ) : 0 < SzemerediRegularity.bound ε l := by positivity

end Tactic

