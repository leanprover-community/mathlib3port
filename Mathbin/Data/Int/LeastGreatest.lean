/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathbin.Data.Int.Order.Basic

/-! # Least upper bound and greatest lower bound properties for integers

In this file we prove that a bounded above nonempty set of integers has the greatest element, and a
counterpart of this statement for the least element.

## Main definitions

* `int.least_of_bdd`: if `P : ℤ → Prop` is a decidable predicate, `b` is a lower bound of the set
  `{m | P m}`, and there exists `m : ℤ` such that `P m` (this time, no witness is required), then
  `int.least_of_bdd` returns the least number `m` such that `P m`, together with proofs of `P m` and
  of the minimality. This definition is computable and does not rely on the axiom of choice.
* `int.greatest_of_bdd`: a similar definition with all inequalities reversed.

## Main statements

* `int.exists_least_of_bdd`: if `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is
  bounded below and nonempty, then this set has the least element. This lemma uses classical logic
  to avoid assumption `[decidable_pred P]`. See `int.least_of_bdd` for a constructive counterpart.

* `int.coe_least_of_bdd_eq`: `(int.least_of_bdd b Hb Hinh : ℤ)` does not depend on `b`.

* `int.exists_greatest_of_bdd`, `int.coe_greatest_of_bdd_eq`: versions of the above lemmas with all
  inequalities reversed.

## Tags

integer numbers, least element, greatest element
-/


namespace Int

/-- A computable version of `exists_least_of_bdd`: given a decidable predicate on the
integers, with an explicit lower bound and a proof that it is somewhere true, return
the least value for which the predicate is true. -/
def leastOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z) (Hinh : ∃ z : ℤ, P z) :
    { lb : ℤ // P lb ∧ ∀ z : ℤ, P z → lb ≤ z } :=
  have EX : ∃ n : ℕ, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : ℤ), Nat.find_spec EX, fun z h =>
    match z, le.dest (Hb _ h), h with
    | _, ⟨n, rfl⟩, h => add_le_add_left (Int.coe_nat_le.2 $ Nat.find_min' _ h) _⟩
#align int.least_of_bdd Int.leastOfBdd

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded below and nonempty,\nthen this set has the least element. This lemma uses classical logic to avoid assumption\n`[decidable_pred P]`. See `int.least_of_bdd` for a constructive counterpart. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_least_of_bdd [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`P]
         [":" (Term.arrow (Init.Data.Int.Basic.termℤ "ℤ") "→" (Init.Core.termProp "Prop"))]
         "}")
        (Term.explicitBinder
         "("
         [`Hbdd]
         [":"
          (Init.Logic.«term∃_,_»
           "∃"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [(group ":" (Init.Data.Int.Basic.termℤ "ℤ"))]))
           ", "
           (Term.forall
            "∀"
            [`z]
            [(Term.typeSpec ":" (Init.Data.Int.Basic.termℤ "ℤ"))]
            ","
            (Term.arrow (Term.app `P [`z]) "→" (Init.Core.«term_≤_» `b " ≤ " `z))))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`Hinh]
         [":"
          (Init.Logic.«term∃_,_»
           "∃"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `z) [(group ":" (Init.Data.Int.Basic.termℤ "ℤ"))]))
           ", "
           (Term.app `P [`z]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Init.Logic.«term∃_,_»
         "∃"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `lb) [(group ":" (Init.Data.Int.Basic.termℤ "ℤ"))]))
         ", "
         (Init.Logic.«term_∧_»
          (Term.app `P [`lb])
          " ∧ "
          (Term.forall
           "∀"
           [`z]
           [(Term.typeSpec ":" (Init.Data.Int.Basic.termℤ "ℤ"))]
           ","
           (Term.arrow (Term.app `P [`z]) "→" (Init.Core.«term_≤_» `lb " ≤ " `z)))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.let
              "let"
              (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
              []
              (Term.let
               "let"
               (Term.letDecl
                (Term.letPatDecl
                 (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
                 []
                 []
                 ":="
                 (Term.app `least_of_bdd [`b `Hb `Hinh])))
               []
               (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")))))])))
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
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact
            "exact"
            (Term.let
             "let"
             (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
             []
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
                []
                []
                ":="
                (Term.app `least_of_bdd [`b `Hb `Hinh])))
              []
              (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.let
         "let"
         (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
         []
         (Term.let
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
            []
            []
            ":="
            (Term.app `least_of_bdd [`b `Hb `Hinh])))
          []
          (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.let
        "let"
        (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
        []
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
           []
           []
           ":="
           (Term.app `least_of_bdd [`b `Hb `Hinh])))
         []
         (Term.anonymousCtor "⟨" [`lb "," `H] "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
       []
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl (Term.anonymousCtor "⟨" [`lb "," `H] "⟩") [] [] ":=" (Term.app `least_of_bdd [`b `Hb `Hinh])))
        []
        (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl (Term.anonymousCtor "⟨" [`lb "," `H] "⟩") [] [] ":=" (Term.app `least_of_bdd [`b `Hb `Hinh])))
       []
       (Term.anonymousCtor "⟨" [`lb "," `H] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `least_of_bdd [`b `Hb `Hinh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hinh
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `least_of_bdd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hbdd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded below and nonempty,
    then this set has the least element. This lemma uses classical logic to avoid assumption
    `[decidable_pred P]`. See `int.least_of_bdd` for a constructive counterpart. -/
  theorem
    exists_least_of_bdd
    { P : ℤ → Prop } ( Hbdd : ∃ b : ℤ , ∀ z : ℤ , P z → b ≤ z ) ( Hinh : ∃ z : ℤ , P z )
      : ∃ lb : ℤ , P lb ∧ ∀ z : ℤ , P z → lb ≤ z
    := by skip <;> exact let ⟨ b , Hb ⟩ := Hbdd let ⟨ lb , H ⟩ := least_of_bdd b Hb Hinh ⟨ lb , H ⟩
#align int.exists_least_of_bdd Int.exists_least_of_bdd

theorem coe_least_of_bdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ} (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hb' : ∀ z : ℤ, P z → b' ≤ z) (Hinh : ∃ z : ℤ, P z) : (leastOfBdd b Hb Hinh : ℤ) = leastOfBdd b' Hb' Hinh := by
  rcases least_of_bdd b Hb Hinh with ⟨n, hn, h2n⟩
  rcases least_of_bdd b' Hb' Hinh with ⟨n', hn', h2n'⟩
  exact le_antisymm (h2n _ hn') (h2n' _ hn)
#align int.coe_least_of_bdd_eq Int.coe_least_of_bdd_eq

/-- A computable version of `exists_greatest_of_bdd`: given a decidable predicate on the
integers, with an explicit upper bound and a proof that it is somewhere true, return
the greatest value for which the predicate is true. -/
def greatestOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → z ≤ b) (Hinh : ∃ z : ℤ, P z) :
    { ub : ℤ // P ub ∧ ∀ z : ℤ, P z → z ≤ ub } :=
  have Hbdd' : ∀ z : ℤ, P (-z) → -b ≤ z := fun z h => neg_le.1 (Hb _ h)
  have Hinh' : ∃ z : ℤ, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg] <;> exact Helt⟩
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
  ⟨-lb, Plb, fun z h => le_neg.1 $ al _ $ by rwa [neg_neg]⟩
#align int.greatest_of_bdd Int.greatestOfBdd

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded above and nonempty,\nthen this set has the greatest element. This lemma uses classical logic to avoid assumption\n`[decidable_pred P]`. See `int.greatest_of_bdd` for a constructive counterpart. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_greatest_of_bdd [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`P]
         [":" (Term.arrow (Init.Data.Int.Basic.termℤ "ℤ") "→" (Init.Core.termProp "Prop"))]
         "}")
        (Term.explicitBinder
         "("
         [`Hbdd]
         [":"
          (Init.Logic.«term∃_,_»
           "∃"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `b) [(group ":" (Init.Data.Int.Basic.termℤ "ℤ"))]))
           ", "
           (Term.forall
            "∀"
            [`z]
            [(Term.typeSpec ":" (Init.Data.Int.Basic.termℤ "ℤ"))]
            ","
            (Term.arrow (Term.app `P [`z]) "→" (Init.Core.«term_≤_» `z " ≤ " `b))))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`Hinh]
         [":"
          (Init.Logic.«term∃_,_»
           "∃"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `z) [(group ":" (Init.Data.Int.Basic.termℤ "ℤ"))]))
           ", "
           (Term.app `P [`z]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Init.Logic.«term∃_,_»
         "∃"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `ub) [(group ":" (Init.Data.Int.Basic.termℤ "ℤ"))]))
         ", "
         (Init.Logic.«term_∧_»
          (Term.app `P [`ub])
          " ∧ "
          (Term.forall
           "∀"
           [`z]
           [(Term.typeSpec ":" (Init.Data.Int.Basic.termℤ "ℤ"))]
           ","
           (Term.arrow (Term.app `P [`z]) "→" (Init.Core.«term_≤_» `z " ≤ " `ub)))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.let
              "let"
              (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
              []
              (Term.let
               "let"
               (Term.letDecl
                (Term.letPatDecl
                 (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
                 []
                 []
                 ":="
                 (Term.app `greatest_of_bdd [`b `Hb `Hinh])))
               []
               (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")))))])))
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
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact
            "exact"
            (Term.let
             "let"
             (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
             []
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
                []
                []
                ":="
                (Term.app `greatest_of_bdd [`b `Hb `Hinh])))
              []
              (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.let
         "let"
         (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
         []
         (Term.let
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
            []
            []
            ":="
            (Term.app `greatest_of_bdd [`b `Hb `Hinh])))
          []
          (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.let
        "let"
        (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
        []
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
           []
           []
           ":="
           (Term.app `greatest_of_bdd [`b `Hb `Hinh])))
         []
         (Term.anonymousCtor "⟨" [`lb "," `H] "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩") [] [] ":=" `Hbdd))
       []
       (Term.let
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
          []
          []
          ":="
          (Term.app `greatest_of_bdd [`b `Hb `Hinh])))
        []
        (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
         []
         []
         ":="
         (Term.app `greatest_of_bdd [`b `Hb `Hinh])))
       []
       (Term.anonymousCtor "⟨" [`lb "," `H] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `greatest_of_bdd [`b `Hb `Hinh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hinh
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `greatest_of_bdd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`lb "," `H] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hbdd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," `Hb] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Hb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded above and nonempty,
    then this set has the greatest element. This lemma uses classical logic to avoid assumption
    `[decidable_pred P]`. See `int.greatest_of_bdd` for a constructive counterpart. -/
  theorem
    exists_greatest_of_bdd
    { P : ℤ → Prop } ( Hbdd : ∃ b : ℤ , ∀ z : ℤ , P z → z ≤ b ) ( Hinh : ∃ z : ℤ , P z )
      : ∃ ub : ℤ , P ub ∧ ∀ z : ℤ , P z → z ≤ ub
    := by skip <;> exact let ⟨ b , Hb ⟩ := Hbdd let ⟨ lb , H ⟩ := greatest_of_bdd b Hb Hinh ⟨ lb , H ⟩
#align int.exists_greatest_of_bdd Int.exists_greatest_of_bdd

theorem coe_greatest_of_bdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ} (Hb : ∀ z : ℤ, P z → z ≤ b)
    (Hb' : ∀ z : ℤ, P z → z ≤ b') (Hinh : ∃ z : ℤ, P z) : (greatestOfBdd b Hb Hinh : ℤ) = greatestOfBdd b' Hb' Hinh :=
  by
  rcases greatest_of_bdd b Hb Hinh with ⟨n, hn, h2n⟩
  rcases greatest_of_bdd b' Hb' Hinh with ⟨n', hn', h2n'⟩
  exact le_antisymm (h2n' _ hn) (h2n _ hn')
#align int.coe_greatest_of_bdd_eq Int.coe_greatest_of_bdd_eq

end Int

