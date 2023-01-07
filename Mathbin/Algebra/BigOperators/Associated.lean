/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen

! This file was ported from Lean 3 source module algebra.big_operators.associated
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.Algebra.BigOperators.Finsupp

/-!
# Products of associated, prime, and irreducible elements.

This file contains some theorems relating definitions in `algebra.associated`
and products of multisets, finsets, and finsupps.

-/


variable {α β γ δ : Type _}

-- mathport name: «expr ~ᵤ »
-- the same local notation used in `algebra.associated`
local infixl:50 " ~ᵤ " => Associated

open BigOperators

namespace Prime

variable [CommMonoidWithZero α] {p : α} (hp : Prime p)

theorem exists_mem_multiset_dvd {s : Multiset α} : p ∣ s.Prod → ∃ a ∈ s, p ∣ a :=
  (Multiset.induction_on s fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.Prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩
#align prime.exists_mem_multiset_dvd Prime.exists_mem_multiset_dvd

include hp

theorem exists_mem_multiset_map_dvd {s : Multiset β} {f : β → α} :
    p ∣ (s.map f).Prod → ∃ a ∈ s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h
#align prime.exists_mem_multiset_map_dvd Prime.exists_mem_multiset_map_dvd

theorem exists_mem_finset_dvd {s : Finset β} {f : β → α} : p ∣ s.Prod f → ∃ i ∈ s, p ∣ f i :=
  hp.exists_mem_multiset_map_dvd
#align prime.exists_mem_finset_dvd Prime.exists_mem_finset_dvd

end Prime

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_associated_mem_of_dvd_prod [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `CancelCommMonoidWithZero [`α]) "]")
        (Term.implicitBinder "{" [`p] [":" `α] "}")
        (Term.explicitBinder "(" [`hp] [":" (Term.app `Prime [`p])] [] ")")
        (Term.implicitBinder "{" [`s] [":" (Term.app `Multiset [`α])] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Std.ExtendedBinder.«term∀__,_»
          "∀"
          (Lean.binderIdent `r)
          («binderTerm∈_» "∈" `s)
          ","
          (Term.app `Prime [`r]))
         "→"
         (Term.arrow
          («term_∣_» `p "∣" (Term.proj `s "." `Prod))
          "→"
          (Std.ExtendedBinder.«term∃__,_»
           "∃"
           (Lean.binderIdent `q)
           («binderTerm∈_» "∈" `s)
           ","
           (Algebra.BigOperators.Associated.«term_~ᵤ_» `p " ~ᵤ " `q))))))
      (Command.declValSimple
       ":="
       (Term.app
        `Multiset.induction_on
        [`s
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
               [(Tactic.simpLemma
                 []
                 []
                 (Term.app `mt [(Term.proj `isUnit_iff_dvd_one "." (fieldIdx "2")) `hp.not_unit]))]
               "]"]
              [])])))
         (Term.fun
          "fun"
          (Term.basicFun
           [`a `s `ih `hs `hps]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Multiset.prod_cons)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hps] []))])
               []
               (Tactic.cases'
                "cases'"
                [(Tactic.casesTarget [] (Term.app `hp.dvd_or_dvd [`hps]))]
                []
                ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hap []]
                    []
                    ":="
                    (Term.app
                     `hs
                     [`a
                      (Term.app
                       (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                       [(Term.app `Or.inl [`rfl])])]))))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [`a
                    ","
                    (Term.app `Multiset.mem_cons_self [`a (Term.hole "_")])
                    ","
                    (Term.app `hp.associated_of_dvd [`hap `h])]
                   "⟩"))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget
                    []
                    (Term.app
                     `ih
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`r `hr]
                        []
                        "=>"
                        (Term.app
                         `hs
                         [(Term.hole "_")
                          (Term.app
                           (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                           [(Term.app `Or.inr [`hr])])])))
                      `h]))]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₁)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₂)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [`q
                    ","
                    (Term.app
                     (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                     [(Term.app `Or.inr [`hq₁])])
                    ","
                    `hq₂]
                   "⟩"))])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Multiset.induction_on
       [`s
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
              [(Tactic.simpLemma
                []
                []
                (Term.app `mt [(Term.proj `isUnit_iff_dvd_one "." (fieldIdx "2")) `hp.not_unit]))]
              "]"]
             [])])))
        (Term.fun
         "fun"
         (Term.basicFun
          [`a `s `ih `hs `hps]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Multiset.prod_cons)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`hps] []))])
              []
              (Tactic.cases'
               "cases'"
               [(Tactic.casesTarget [] (Term.app `hp.dvd_or_dvd [`hps]))]
               []
               ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hap []]
                   []
                   ":="
                   (Term.app
                    `hs
                    [`a
                     (Term.app
                      (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                      [(Term.app `Or.inl [`rfl])])]))))
                []
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [`a
                   ","
                   (Term.app `Multiset.mem_cons_self [`a (Term.hole "_")])
                   ","
                   (Term.app `hp.associated_of_dvd [`hap `h])]
                  "⟩"))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    `ih
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`r `hr]
                       []
                       "=>"
                       (Term.app
                        `hs
                        [(Term.hole "_")
                         (Term.app
                          (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                          [(Term.app `Or.inr [`hr])])])))
                     `h]))]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₁)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₂)])
                        [])]
                      "⟩")])
                   [])])
                []
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [`q
                   ","
                   (Term.app
                    (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                    [(Term.app `Or.inr [`hq₁])])
                   ","
                   `hq₂]
                  "⟩"))])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `s `ih `hs `hps]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Multiset.prod_cons)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hps] []))])
            []
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] (Term.app `hp.dvd_or_dvd [`hps]))]
             []
             ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hap []]
                 []
                 ":="
                 (Term.app
                  `hs
                  [`a
                   (Term.app
                    (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                    [(Term.app `Or.inl [`rfl])])]))))
              []
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`a
                 ","
                 (Term.app `Multiset.mem_cons_self [`a (Term.hole "_")])
                 ","
                 (Term.app `hp.associated_of_dvd [`hap `h])]
                "⟩"))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  `ih
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`r `hr]
                     []
                     "=>"
                     (Term.app
                      `hs
                      [(Term.hole "_")
                       (Term.app
                        (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                        [(Term.app `Or.inr [`hr])])])))
                   `h]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₂)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`q
                 ","
                 (Term.app
                  (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                  [(Term.app `Or.inr [`hq₁])])
                 ","
                 `hq₂]
                "⟩"))])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Multiset.prod_cons)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hps] []))])
          []
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] (Term.app `hp.dvd_or_dvd [`hps]))]
           []
           ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hap []]
               []
               ":="
               (Term.app
                `hs
                [`a
                 (Term.app
                  (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                  [(Term.app `Or.inl [`rfl])])]))))
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [`a
               ","
               (Term.app `Multiset.mem_cons_self [`a (Term.hole "_")])
               ","
               (Term.app `hp.associated_of_dvd [`hap `h])]
              "⟩"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                `ih
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`r `hr]
                   []
                   "=>"
                   (Term.app
                    `hs
                    [(Term.hole "_")
                     (Term.app
                      (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                      [(Term.app `Or.inr [`hr])])])))
                 `h]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₂)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [`q
               ","
               (Term.app
                (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                [(Term.app `Or.inr [`hq₁])])
               ","
               `hq₂]
              "⟩"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget
           []
           (Term.app
            `ih
            [(Term.fun
              "fun"
              (Term.basicFun
               [`r `hr]
               []
               "=>"
               (Term.app
                `hs
                [(Term.hole "_")
                 (Term.app
                  (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                  [(Term.app `Or.inr [`hr])])])))
             `h]))]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₂)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`q
           ","
           (Term.app (Term.proj `Multiset.mem_cons "." (fieldIdx "2")) [(Term.app `Or.inr [`hq₁])])
           ","
           `hq₂]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`q
         ","
         (Term.app (Term.proj `Multiset.mem_cons "." (fieldIdx "2")) [(Term.app `Or.inr [`hq₁])])
         ","
         `hq₂]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`q
        ","
        (Term.app (Term.proj `Multiset.mem_cons "." (fieldIdx "2")) [(Term.app `Or.inr [`hq₁])])
        ","
        `hq₂]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hq₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Multiset.mem_cons "." (fieldIdx "2")) [(Term.app `Or.inr [`hq₁])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inr [`hq₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hq₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Or.inr [`hq₁]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Multiset.mem_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app
          `ih
          [(Term.fun
            "fun"
            (Term.basicFun
             [`r `hr]
             []
             "=>"
             (Term.app
              `hs
              [(Term.hole "_")
               (Term.app
                (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
                [(Term.app `Or.inr [`hr])])])))
           `h]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `q)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₁)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hq₂)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ih
       [(Term.fun
         "fun"
         (Term.basicFun
          [`r `hr]
          []
          "=>"
          (Term.app
           `hs
           [(Term.hole "_")
            (Term.app
             (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
             [(Term.app `Or.inr [`hr])])])))
        `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`r `hr]
        []
        "=>"
        (Term.app
         `hs
         [(Term.hole "_")
          (Term.app
           (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
           [(Term.app `Or.inr [`hr])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hs
       [(Term.hole "_")
        (Term.app (Term.proj `Multiset.mem_cons "." (fieldIdx "2")) [(Term.app `Or.inr [`hr])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Multiset.mem_cons "." (fieldIdx "2")) [(Term.app `Or.inr [`hr])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inr [`hr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Or.inr [`hr]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Multiset.mem_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
      [(Term.paren "(" (Term.app `Or.inr [`hr]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`r `hr]
       []
       "=>"
       (Term.app
        `hs
        [(Term.hole "_")
         (Term.paren
          "("
          (Term.app
           (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
           [(Term.paren "(" (Term.app `Or.inr [`hr]) ")")])
          ")")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hap []]
           []
           ":="
           (Term.app
            `hs
            [`a
             (Term.app
              (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
              [(Term.app `Or.inl [`rfl])])]))))
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [`a
           ","
           (Term.app `Multiset.mem_cons_self [`a (Term.hole "_")])
           ","
           (Term.app `hp.associated_of_dvd [`hap `h])]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`a
         ","
         (Term.app `Multiset.mem_cons_self [`a (Term.hole "_")])
         ","
         (Term.app `hp.associated_of_dvd [`hap `h])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`a
        ","
        (Term.app `Multiset.mem_cons_self [`a (Term.hole "_")])
        ","
        (Term.app `hp.associated_of_dvd [`hap `h])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hp.associated_of_dvd [`hap `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hap
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hp.associated_of_dvd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Multiset.mem_cons_self [`a (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiset.mem_cons_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hap []]
         []
         ":="
         (Term.app
          `hs
          [`a
           (Term.app
            (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
            [(Term.app `Or.inl [`rfl])])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hs
       [`a
        (Term.app (Term.proj `Multiset.mem_cons "." (fieldIdx "2")) [(Term.app `Or.inl [`rfl])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Multiset.mem_cons "." (fieldIdx "2")) [(Term.app `Or.inl [`rfl])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Or.inl [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.inl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Or.inl [`rfl]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Multiset.mem_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `Multiset.mem_cons "." (fieldIdx "2"))
      [(Term.paren "(" (Term.app `Or.inl [`rfl]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] (Term.app `hp.dvd_or_dvd [`hps]))]
       []
       ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hp.dvd_or_dvd [`hps])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hps
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hp.dvd_or_dvd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Multiset.prod_cons)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hps] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hps
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.prod_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hps
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
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
            [(Tactic.simpLemma
              []
              []
              (Term.app `mt [(Term.proj `isUnit_iff_dvd_one "." (fieldIdx "2")) `hp.not_unit]))]
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
        [(Tactic.simpLemma
          []
          []
          (Term.app `mt [(Term.proj `isUnit_iff_dvd_one "." (fieldIdx "2")) `hp.not_unit]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mt [(Term.proj `isUnit_iff_dvd_one "." (fieldIdx "2")) `hp.not_unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.not_unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `isUnit_iff_dvd_one "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `isUnit_iff_dvd_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
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
           [(Tactic.simpLemma
             []
             []
             (Term.app `mt [(Term.proj `isUnit_iff_dvd_one "." (fieldIdx "2")) `hp.not_unit]))]
           "]"]
          [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiset.induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Std.ExtendedBinder.«term∀__,_»
        "∀"
        (Lean.binderIdent `r)
        («binderTerm∈_» "∈" `s)
        ","
        (Term.app `Prime [`r]))
       "→"
       (Term.arrow
        («term_∣_» `p "∣" (Term.proj `s "." `Prod))
        "→"
        (Std.ExtendedBinder.«term∃__,_»
         "∃"
         (Lean.binderIdent `q)
         («binderTerm∈_» "∈" `s)
         ","
         (Algebra.BigOperators.Associated.«term_~ᵤ_» `p " ~ᵤ " `q))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       («term_∣_» `p "∣" (Term.proj `s "." `Prod))
       "→"
       (Std.ExtendedBinder.«term∃__,_»
        "∃"
        (Lean.binderIdent `q)
        («binderTerm∈_» "∈" `s)
        ","
        (Algebra.BigOperators.Associated.«term_~ᵤ_» `p " ~ᵤ " `q)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∃__,_»
       "∃"
       (Lean.binderIdent `q)
       («binderTerm∈_» "∈" `s)
       ","
       (Algebra.BigOperators.Associated.«term_~ᵤ_» `p " ~ᵤ " `q))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.BigOperators.Associated.«term_~ᵤ_» `p " ~ᵤ " `q)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Associated.«term_~ᵤ_»', expected 'Algebra.BigOperators.Associated.term_~ᵤ_._@.Algebra.BigOperators.Associated._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  exists_associated_mem_of_dvd_prod
  [ CancelCommMonoidWithZero α ] { p : α } ( hp : Prime p ) { s : Multiset α }
    : ∀ r ∈ s , Prime r → p ∣ s . Prod → ∃ q ∈ s , p ~ᵤ q
  :=
    Multiset.induction_on
      s
        by simp [ mt isUnit_iff_dvd_one . 2 hp.not_unit ]
        fun
          a s ih hs hps
            =>
            by
              rw [ Multiset.prod_cons ] at hps
                cases' hp.dvd_or_dvd hps with h h
                ·
                  have hap := hs a Multiset.mem_cons . 2 Or.inl rfl
                    exact ⟨ a , Multiset.mem_cons_self a _ , hp.associated_of_dvd hap h ⟩
                ·
                  rcases
                      ih fun r hr => hs _ Multiset.mem_cons . 2 Or.inr hr h
                      with ⟨ q , hq₁ , hq₂ ⟩
                    exact ⟨ q , Multiset.mem_cons . 2 Or.inr hq₁ , hq₂ ⟩
#align exists_associated_mem_of_dvd_prod exists_associated_mem_of_dvd_prod

theorem Multiset.prod_primes_dvd [CancelCommMonoidWithZero α]
    [∀ a : α, DecidablePred (Associated a)] {s : Multiset α} (n : α) (h : ∀ a ∈ s, Prime a)
    (div : ∀ a ∈ s, a ∣ n) (uniq : ∀ a, s.countp (Associated a) ≤ 1) : s.Prod ∣ n :=
  by
  induction' s using Multiset.induction_on with a s induct n primes divs generalizing n
  · simp only [Multiset.prod_zero, one_dvd]
  · rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    apply mul_dvd_mul_left a
    refine'
      induct (fun a ha => h a (Multiset.mem_cons_of_mem ha))
        (fun a => (Multiset.countp_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)) k
        fun b b_in_s => _
    · have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
      have a_prime := h a (Multiset.mem_cons_self a s)
      have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
      refine' (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => _
      have assoc := b_prime.associated_of_dvd a_prime b_div_a
      have := uniq a
      rw [Multiset.countp_cons_of_pos _ (Associated.refl _), Nat.succ_le_succ_iff, ← not_lt,
        Multiset.countp_pos] at this
      exact this ⟨b, b_in_s, assoc.symm⟩
#align multiset.prod_primes_dvd Multiset.prod_primes_dvd

theorem Finset.prod_primes_dvd [CancelCommMonoidWithZero α] [Unique αˣ] {s : Finset α} (n : α)
    (h : ∀ a ∈ s, Prime a) (div : ∀ a ∈ s, a ∣ n) : (∏ p in s, p) ∣ n := by
  classical exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countp_eq_card_filter, ←
            Multiset.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])
#align finset.prod_primes_dvd Finset.prod_primes_dvd

namespace Associates

section CommMonoid

variable [CommMonoid α]

theorem prod_mk {p : Multiset α} : (p.map Associates.mk).Prod = Associates.mk p.Prod :=
  (Multiset.induction_on p (by simp)) fun a s ih => by simp [ih, Associates.mk_mul_mk]
#align associates.prod_mk Associates.prod_mk

theorem finset_prod_mk {p : Finset β} {f : β → α} :
    (∏ i in p, Associates.mk (f i)) = Associates.mk (∏ i in p, f i) := by
  rw [Finset.prod_eq_multiset_prod, ← Multiset.map_map, prod_mk, ← Finset.prod_eq_multiset_prod]
#align associates.finset_prod_mk Associates.finset_prod_mk

theorem rel_associated_iff_map_eq_map {p q : Multiset α} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk :=
  by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]
#align associates.rel_associated_iff_map_eq_map Associates.rel_associated_iff_map_eq_map

theorem prod_eq_one_iff {p : Multiset (Associates α)} :
    p.Prod = 1 ↔ ∀ a ∈ p, (a : Associates α) = 1 :=
  Multiset.induction_on p (by simp)
    (by simp (config := { contextual := true }) [mul_eq_one_iff, or_imp, forall_and])
#align associates.prod_eq_one_iff Associates.prod_eq_one_iff

theorem prod_le_prod {p q : Multiset (Associates α)} (h : p ≤ q) : p.Prod ≤ q.Prod :=
  by
  haveI := Classical.decEq (Associates α)
  haveI := Classical.decEq α
  suffices p.prod ≤ (p + (q - p)).Prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 ≤ p.prod * (q - p).Prod by simpa
  exact mul_mono (le_refl p.prod) one_le
#align associates.prod_le_prod Associates.prod_le_prod

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates α)} {p : Associates α}
    (hp : Prime p) : p ≤ s.Prod → ∃ a ∈ s, p ≤ a :=
  (Multiset.induction_on s fun ⟨d, Eq⟩ => (hp.ne_one (mul_eq_one_iff.1 Eq.symm).1).elim)
    fun a s ih h =>
    have : p ≤ a * s.Prod := by simpa using h
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩
#align associates.exists_mem_multiset_le_of_prime Associates.exists_mem_multiset_le_of_prime

end CancelCommMonoidWithZero

end Associates

namespace Multiset

theorem prod_ne_zero_of_prime [CancelCommMonoidWithZero α] [Nontrivial α] (s : Multiset α)
    (h : ∀ x ∈ s, Prime x) : s.Prod ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl
#align multiset.prod_ne_zero_of_prime Multiset.prod_ne_zero_of_prime

end Multiset

open Finset Finsupp

section CommMonoidWithZero

variable {M : Type _} [CommMonoidWithZero M]

theorem Prime.dvd_finset_prod_iff {S : Finset α} {p : M} (pp : Prime p) (g : α → M) :
    p ∣ S.Prod g ↔ ∃ a ∈ S, p ∣ g a :=
  ⟨pp.exists_mem_finset_dvd, fun ⟨a, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩
#align prime.dvd_finset_prod_iff Prime.dvd_finset_prod_iff

theorem Prime.dvd_finsupp_prod_iff {f : α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : Prime p) :
    p ∣ f.Prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
  Prime.dvd_finset_prod_iff pp _
#align prime.dvd_finsupp_prod_iff Prime.dvd_finsupp_prod_iff

end CommMonoidWithZero

