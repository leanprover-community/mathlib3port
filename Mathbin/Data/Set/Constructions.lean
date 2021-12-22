import Mathbin.Data.Finset.Basic

/-!
# Constructions involving sets of sets.

## Finite Intersections

We define a structure `has_finite_inter` which asserts that a set `S` of subsets of `α` is
closed under finite intersections.

We define `finite_inter_closure` which, given a set `S` of subsets of `α`, is the smallest
set of subsets of `α` which is closed under finite intersections.

`finite_inter_closure S` is endowed with a term of type `has_finite_inter` using
`finite_inter_closure_has_finite_inter`.

-/


variable {α : Type _} (S : Set (Set α))

/--  A structure encapsulating the fact that a set of sets is closed under finite intersection. -/
structure HasFiniteInter where
  univ_mem : Set.Univ ∈ S
  inter_mem {s t} : s ∈ S → t ∈ S → s ∩ t ∈ S

namespace HasFiniteInter

instance : Inhabited (HasFiniteInter ({Set.Univ} : Set (Set α))) :=
  ⟨⟨by
      tauto, fun _ _ h1 h2 => by
      simp [Set.mem_singleton_iff.1 h1, Set.mem_singleton_iff.1 h2]⟩⟩

/--  The smallest set of sets containing `S` which is closed under finite intersections. -/
inductive finite_inter_closure : Set (Set α)
  | basic {s} : s ∈ S → finite_inter_closure s
  | univ : finite_inter_closure Set.Univ
  | inter {s t} : finite_inter_closure s → finite_inter_closure t → finite_inter_closure (s ∩ t)

/--  Defines `has_finite_inter` for `finite_inter_closure S`. -/
def finite_inter_closure_has_finite_inter : HasFiniteInter (finite_inter_closure S) :=
  { univ_mem := finite_inter_closure.univ, inter_mem := fun _ _ => finite_inter_closure.inter }

variable {S}

theorem finite_inter_mem (cond : HasFiniteInter S) (F : Finset (Set α)) : ↑F ⊆ S → ⋂₀(↑F : Set (Set α)) ∈ S := by
  classical
  refine' Finset.induction_on F (fun _ => _) _
  ·
    simp [cond.univ_mem]
  ·
    intro a s h1 h2 h3
    suffices a ∩ ⋂₀↑s ∈ S by
      simpa
    exact cond.inter_mem (h3 (Finset.mem_insert_self a s)) (h2 $ fun x hx => h3 $ Finset.mem_insert_of_mem hx)

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (P «expr ∈ » finite_inter_closure (insert A S))
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `finite_inter_closure_insert [])
  (Command.declSig
   [(Term.implicitBinder "{" [`A] [":" (Term.app `Set [`α])] "}")
    (Term.explicitBinder "(" [`cond] [":" (Term.app `HasFiniteInter [`S])] [] ")")
    (Term.simpleBinder [`P] [])
    (Term.explicitBinder
     "("
     [(Term.hole "_")]
     [":" (Init.Core.«term_∈_» `P " ∈ " (Term.app `finite_inter_closure [(Term.app `insert [`A `S])]))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_∨_»
     (Init.Core.«term_∈_» `P " ∈ " `S)
     "∨"
     (Mathlib.ExtendedBinder.«term∃___,_»
      "∃"
      `Q
      («binderTerm∈_» "∈" `S)
      ","
      («term_=_» `P "=" (Init.Core.«term_∩_» `A " ∩ " `Q))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.induction'
         "induction'"
         [(Tactic.casesTarget [] `H)]
         []
         ["with"
          [(Lean.binderIdent `S)
           (Lean.binderIdent `h)
           (Lean.binderIdent `T1)
           (Lean.binderIdent `T2)
           (Lean.binderIdent "_")
           (Lean.binderIdent "_")
           (Lean.binderIdent `h1)
           (Lean.binderIdent `h2)]]
         [])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `Or.inr
                    [(Term.anonymousCtor
                      "⟨"
                      [`Set.Univ
                       ","
                       `cond.univ_mem
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))]
                      "⟩")]))
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `Or.inl [`h])) [])])))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `Or.inl [`cond.univ_mem])) [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.«tactic_<;>_»
              (Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `h1)]
               ["with"
                (Tactic.rcasesPat.paren
                 "("
                 (Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed
                   [(Tactic.rcasesPat.one `h)
                    "|"
                    (Tactic.rcasesPat.tuple
                     "⟨"
                     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Q)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hQ)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                     "⟩")])
                  [])
                 ")")])
              "<;>"
              (Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `h2)]
               ["with"
                (Tactic.rcasesPat.paren
                 "("
                 (Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed
                   [(Tactic.rcasesPat.one `i)
                    "|"
                    (Tactic.rcasesPat.tuple
                     "⟨"
                     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `R)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hR)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                     "⟩")])
                  [])
                 ")")]))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.exact "exact" (Term.app `Or.inl [(Term.app `cond.inter_mem [`h `i])])) [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `Or.inr
                    [(Term.anonymousCtor
                      "⟨"
                      [(Init.Core.«term_∩_» `T1 " ∩ " `R)
                       ","
                       (Term.app `cond.inter_mem [`h `hR])
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.simp
                             "simp"
                             []
                             ["only"]
                             ["["
                              [(Tactic.simpLemma [] ["←"] `Set.inter_assoc)
                               ","
                               (Tactic.simpLemma [] [] (Term.app `Set.inter_comm [(Term.hole "_") `A]))]
                              "]"]
                             [])
                            [])])))]
                      "⟩")]))
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `Or.inr
                    [(Term.anonymousCtor
                      "⟨"
                      [(Init.Core.«term_∩_» `Q " ∩ " `T2)
                       ","
                       (Term.app `cond.inter_mem [`hQ `i])
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.inter_assoc)] "]"] [])
                            [])])))]
                      "⟩")]))
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `Or.inr
                    [(Term.anonymousCtor
                      "⟨"
                      [(Init.Core.«term_∩_» `Q " ∩ " `R)
                       ","
                       (Term.app `cond.inter_mem [`hQ `hR])
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                           (group
                            (Tactic.«tactic_<;>_»
                             (Tactic.constructor "constructor")
                             "<;>"
                             (Tactic.simp
                              "simp"
                              ["("
                               "config"
                               ":="
                               (Term.structInst
                                "{"
                                []
                                [(group
                                  (Term.structInstField
                                   (Term.structInstLVal `contextual [])
                                   ":="
                                   `Bool.true._@._internal._hyg.0)
                                  [])]
                                (Term.optEllipsis [])
                                []
                                "}")
                               ")"]
                              []
                              []
                              []))
                            [])])))]
                      "⟩")]))
                  [])])))
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.induction'
        "induction'"
        [(Tactic.casesTarget [] `H)]
        []
        ["with"
         [(Lean.binderIdent `S)
          (Lean.binderIdent `h)
          (Lean.binderIdent `T1)
          (Lean.binderIdent `T2)
          (Lean.binderIdent "_")
          (Lean.binderIdent "_")
          (Lean.binderIdent `h1)
          (Lean.binderIdent `h2)]]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `Or.inr
                   [(Term.anonymousCtor
                     "⟨"
                     [`Set.Univ
                      ","
                      `cond.univ_mem
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))]
                     "⟩")]))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `Or.inl [`h])) [])])))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `Or.inl [`cond.univ_mem])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.«tactic_<;>_»
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `h1)]
              ["with"
               (Tactic.rcasesPat.paren
                "("
                (Tactic.rcasesPatLo
                 (Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.one `h)
                   "|"
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Q)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hQ)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                    "⟩")])
                 [])
                ")")])
             "<;>"
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `h2)]
              ["with"
               (Tactic.rcasesPat.paren
                "("
                (Tactic.rcasesPatLo
                 (Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.one `i)
                   "|"
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `R)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hR)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                    "⟩")])
                 [])
                ")")]))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.exact "exact" (Term.app `Or.inl [(Term.app `cond.inter_mem [`h `i])])) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `Or.inr
                   [(Term.anonymousCtor
                     "⟨"
                     [(Init.Core.«term_∩_» `T1 " ∩ " `R)
                      ","
                      (Term.app `cond.inter_mem [`h `hR])
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.simp
                            "simp"
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] ["←"] `Set.inter_assoc)
                              ","
                              (Tactic.simpLemma [] [] (Term.app `Set.inter_comm [(Term.hole "_") `A]))]
                             "]"]
                            [])
                           [])])))]
                     "⟩")]))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `Or.inr
                   [(Term.anonymousCtor
                     "⟨"
                     [(Init.Core.«term_∩_» `Q " ∩ " `T2)
                      ","
                      (Term.app `cond.inter_mem [`hQ `i])
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.inter_assoc)] "]"] [])
                           [])])))]
                     "⟩")]))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `Or.inr
                   [(Term.anonymousCtor
                     "⟨"
                     [(Init.Core.«term_∩_» `Q " ∩ " `R)
                      ","
                      (Term.app `cond.inter_mem [`hQ `hR])
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                          (group
                           (Tactic.«tactic_<;>_»
                            (Tactic.constructor "constructor")
                            "<;>"
                            (Tactic.simp
                             "simp"
                             ["("
                              "config"
                              ":="
                              (Term.structInst
                               "{"
                               []
                               [(group
                                 (Term.structInstField
                                  (Term.structInstLVal `contextual [])
                                  ":="
                                  `Bool.true._@._internal._hyg.0)
                                 [])]
                               (Term.optEllipsis [])
                               []
                               "}")
                              ")"]
                             []
                             []
                             []))
                           [])])))]
                     "⟩")]))
                 [])])))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `h1)]
         ["with"
          (Tactic.rcasesPat.paren
           "("
           (Tactic.rcasesPatLo
            (Tactic.rcasesPatMed
             [(Tactic.rcasesPat.one `h)
              "|"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Q)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hQ)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
               "⟩")])
            [])
           ")")])
        "<;>"
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `h2)]
         ["with"
          (Tactic.rcasesPat.paren
           "("
           (Tactic.rcasesPatLo
            (Tactic.rcasesPatMed
             [(Tactic.rcasesPat.one `i)
              "|"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `R)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hR)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
               "⟩")])
            [])
           ")")]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.exact "exact" (Term.app `Or.inl [(Term.app `cond.inter_mem [`h `i])])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.app
              `Or.inr
              [(Term.anonymousCtor
                "⟨"
                [(Init.Core.«term_∩_» `T1 " ∩ " `R)
                 ","
                 (Term.app `cond.inter_mem [`h `hR])
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.simp
                       "simp"
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] ["←"] `Set.inter_assoc)
                         ","
                         (Tactic.simpLemma [] [] (Term.app `Set.inter_comm [(Term.hole "_") `A]))]
                        "]"]
                       [])
                      [])])))]
                "⟩")]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.app
              `Or.inr
              [(Term.anonymousCtor
                "⟨"
                [(Init.Core.«term_∩_» `Q " ∩ " `T2)
                 ","
                 (Term.app `cond.inter_mem [`hQ `i])
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.inter_assoc)] "]"] [])
                      [])])))]
                "⟩")]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.app
              `Or.inr
              [(Term.anonymousCtor
                "⟨"
                [(Init.Core.«term_∩_» `Q " ∩ " `R)
                 ","
                 (Term.app `cond.inter_mem [`hQ `hR])
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                     (group
                      (Tactic.«tactic_<;>_»
                       (Tactic.constructor "constructor")
                       "<;>"
                       (Tactic.simp
                        "simp"
                        ["("
                         "config"
                         ":="
                         (Term.structInst
                          "{"
                          []
                          [(group
                            (Term.structInstField
                             (Term.structInstLVal `contextual [])
                             ":="
                             `Bool.true._@._internal._hyg.0)
                            [])]
                          (Term.optEllipsis [])
                          []
                          "}")
                         ")"]
                        []
                        []
                        []))
                      [])])))]
                "⟩")]))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.app
         `Or.inr
         [(Term.anonymousCtor
           "⟨"
           [(Init.Core.«term_∩_» `Q " ∩ " `R)
            ","
            (Term.app `cond.inter_mem [`hQ `hR])
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                (group
                 (Tactic.«tactic_<;>_»
                  (Tactic.constructor "constructor")
                  "<;>"
                  (Tactic.simp
                   "simp"
                   ["("
                    "config"
                    ":="
                    (Term.structInst
                     "{"
                     []
                     [(group
                       (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                       [])]
                     (Term.optEllipsis [])
                     []
                     "}")
                    ")"]
                   []
                   []
                   []))
                 [])])))]
           "⟩")]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `Or.inr
    [(Term.anonymousCtor
      "⟨"
      [(Init.Core.«term_∩_» `Q " ∩ " `R)
       ","
       (Term.app `cond.inter_mem [`hQ `hR])
       ","
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
           (group
            (Tactic.«tactic_<;>_»
             (Tactic.constructor "constructor")
             "<;>"
             (Tactic.simp
              "simp"
              ["("
               "config"
               ":="
               (Term.structInst
                "{"
                []
                [(group
                  (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                  [])]
                (Term.optEllipsis [])
                []
                "}")
               ")"]
              []
              []
              []))
            [])])))]
      "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Or.inr
   [(Term.anonymousCtor
     "⟨"
     [(Init.Core.«term_∩_» `Q " ∩ " `R)
      ","
      (Term.app `cond.inter_mem [`hQ `hR])
      ","
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
          (group
           (Tactic.«tactic_<;>_»
            (Tactic.constructor "constructor")
            "<;>"
            (Tactic.simp
             "simp"
             ["("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                 [])]
               (Term.optEllipsis [])
               []
               "}")
              ")"]
             []
             []
             []))
           [])])))]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Init.Core.«term_∩_» `Q " ∩ " `R)
    ","
    (Term.app `cond.inter_mem [`hQ `hR])
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
        (group
         (Tactic.«tactic_<;>_»
          (Tactic.constructor "constructor")
          "<;>"
          (Tactic.simp
           "simp"
           ["("
            "config"
            ":="
            (Term.structInst
             "{"
             []
             [(group
               (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
               [])]
             (Term.optEllipsis [])
             []
             "}")
            ")"]
           []
           []
           []))
         [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
      (group
       (Tactic.«tactic_<;>_»
        (Tactic.constructor "constructor")
        "<;>"
        (Tactic.simp
         "simp"
         ["("
          "config"
          ":="
          (Term.structInst
           "{"
           []
           [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
           (Term.optEllipsis [])
           []
           "}")
          ")"]
         []
         []
         []))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.constructor "constructor")
   "<;>"
   (Tactic.simp
    "simp"
    ["("
     "config"
     ":="
     (Term.structInst
      "{"
      []
      [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
      (Term.optEllipsis [])
      []
      "}")
     ")"]
    []
    []
    []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   []
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  finite_inter_closure_insert
  { A : Set α } ( cond : HasFiniteInter S ) P ( _ : P ∈ finite_inter_closure insert A S ) : P ∈ S ∨ ∃ Q ∈ S , P = A ∩ Q
  :=
    by
      induction' H with S h T1 T2 _ _ h1 h2
        · cases h · exact Or.inr ⟨ Set.Univ , cond.univ_mem , by simpa ⟩ · exact Or.inl h
        · exact Or.inl cond.univ_mem
        ·
          rcases h1 with ( h | ⟨ Q , hQ , rfl ⟩ ) <;> rcases h2 with ( i | ⟨ R , hR , rfl ⟩ )
            · exact Or.inl cond.inter_mem h i
            · exact Or.inr ⟨ T1 ∩ R , cond.inter_mem h hR , by simp only [ ← Set.inter_assoc , Set.inter_comm _ A ] ⟩
            · exact Or.inr ⟨ Q ∩ T2 , cond.inter_mem hQ i , by simp only [ Set.inter_assoc ] ⟩
            ·
              exact
                Or.inr
                  ⟨
                    Q ∩ R
                      ,
                      cond.inter_mem hQ hR
                      ,
                      by ext x constructor <;> simp ( config := { contextual := Bool.true._@._internal._hyg.0 } )
                    ⟩

end HasFiniteInter

