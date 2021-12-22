import Mathbin.NumberTheory.PythagoreanTriples
import Mathbin.RingTheory.Coprime.Lemmas

/-!
# Fermat's Last Theorem for the case n = 4
There are no non-zero integers `a`, `b` and `c` such that `a ^ 4 + b ^ 4 = c ^ 4`.
-/


noncomputable section

open_locale Classical

/--  Shorthand for three non-zero integers `a`, `b`, and `c` satisfying `a ^ 4 + b ^ 4 = c ^ 2`.
We will show that no integers satisfy this equation. Clearly Fermat's Last theorem for n = 4
follows. -/
def Fermat42 (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ ((a^4)+b^4) = (c^2)

namespace Fermat42

theorem comm {a b c : ℤ} : Fermat42 a b c ↔ Fermat42 b a c := by
  delta' Fermat42
  rw [add_commₓ]
  tauto

theorem mul {a b c k : ℤ} (hk0 : k ≠ 0) : Fermat42 a b c ↔ Fermat42 (k*a) (k*b) ((k^2)*c) := by
  delta' Fermat42
  constructor
  ·
    intro f42
    constructor
    ·
      exact mul_ne_zero hk0 f42.1
    constructor
    ·
      exact mul_ne_zero hk0 f42.2.1
    ·
      calc (((k*a)^4)+(k*b)^4) = (k^4)*(a^4)+b^4 := by
        ring _ = (k^4)*c^2 := by
        rw [f42.2.2]_ = (((k^2)*c)^2) := by
        ring
  ·
    intro f42
    constructor
    ·
      exact right_ne_zero_of_mul f42.1
    constructor
    ·
      exact right_ne_zero_of_mul f42.2.1
    apply (mul_right_inj' (pow_ne_zero 4 hk0)).mp
    ·
      calc ((k^4)*(a^4)+b^4) = ((k*a)^4)+(k*b)^4 := by
        ring _ = (((k^2)*c)^2) := by
        rw [f42.2.2]_ = (k^4)*c^2 := by
        ring

theorem ne_zero {a b c : ℤ} (h : Fermat42 a b c) : c ≠ 0 := by
  apply
    ne_zero_pow
      (by
        decide : 2 ≠ 0)
  apply ne_of_gtₓ
  rw [← h.2.2,
    (by
      ring : ((a^4)+b^4) = ((a^2)^2)+(b^2)^2)]
  exact add_pos (sq_pos_of_ne_zero _ (pow_ne_zero 2 h.1)) (sq_pos_of_ne_zero _ (pow_ne_zero 2 h.2.1))

/--  We say a solution to `a ^ 4 + b ^ 4 = c ^ 2` is minimal if there is no other solution with
a smaller `c` (in absolute value). -/
def minimal (a b c : ℤ) : Prop :=
  Fermat42 a b c ∧ ∀ a1 b1 c1 : ℤ, Fermat42 a1 b1 c1 → Int.natAbs c ≤ Int.natAbs c1

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " if we have a solution to `a ^ 4 + b ^ 4 = c ^ 2` then there must be a minimal one. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `exists_minimal [])
  (Command.declSig
   [(Term.implicitBinder "{" [`a `b `c] [":" (termℤ "ℤ")] "}")
    (Term.explicitBinder "(" [`h] [":" (Term.app `Fermat42 [`a `b `c])] [] ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a0) (Lean.binderIdent `b0) (Lean.binderIdent `c0)] []))
     ","
     (Term.app `minimal [`a0 `b0 `c0]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `S
           [(Term.typeSpec ":" (Term.app `Set [(termℕ "ℕ")]))]
           ":="
           (Set.«term{_|_}»
            "{"
            `n
            "|"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `s)]
               [":" («term_×_» (termℤ "ℤ") "×" («term_×_» (termℤ "ℤ") "×" (termℤ "ℤ")))]))
             ","
             («term_∧_»
              (Term.app
               `Fermat42
               [(Term.proj `s "." (fieldIdx "1"))
                (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
                (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])
              "∧"
              («term_=_»
               `n
               "="
               (Term.app `Int.natAbs [(Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))]))))
            "}"))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`S_nonempty []]
           [(Term.typeSpec ":" `S.nonempty)]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.use "use" [(Term.app `Int.natAbs [`c])]) [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_set_of_eq)] "]") []) [])
               (group
                (Tactic.use "use" [(Term.anonymousCtor "⟨" [`a "," (Term.anonymousCtor "⟨" [`b "," `c] "⟩")] "⟩")])
                [])
               (group (Tactic.tauto "tauto" []) [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl (Term.letIdDecl `m [(Term.typeSpec ":" (termℕ "ℕ"))] ":=" (Term.app `Nat.findₓ [`S_nonempty]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`m_mem []]
           [(Term.typeSpec ":" (Init.Core.«term_∈_» `m " ∈ " `S))]
           ":="
           (Term.app `Nat.find_specₓ [`S_nonempty]))))
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `m_mem)]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s0)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs0)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs1)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.use
         "use"
         [(Term.proj `s0 "." (fieldIdx "1"))
          ","
          (Term.proj (Term.proj `s0 "." (fieldIdx "2")) "." (fieldIdx "1"))
          ","
          (Term.proj (Term.proj `s0 "." (fieldIdx "2")) "." (fieldIdx "2"))
          ","
          `hs0])
        [])
       (group (Tactic.intro "intro" [`a1 `b1 `c1 `h1]) [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hs1)] "]") []) [])
       (group (Tactic.apply "apply" `Nat.find_min'ₓ) [])
       (group (Tactic.use "use" [(Term.anonymousCtor "⟨" [`a1 "," (Term.anonymousCtor "⟨" [`b1 "," `c1] "⟩")] "⟩")]) [])
       (group (Tactic.tauto "tauto" []) [])])))
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
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `S
          [(Term.typeSpec ":" (Term.app `Set [(termℕ "ℕ")]))]
          ":="
          (Set.«term{_|_}»
           "{"
           `n
           "|"
           («term∃_,_»
            "∃"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `s)]
              [":" («term_×_» (termℤ "ℤ") "×" («term_×_» (termℤ "ℤ") "×" (termℤ "ℤ")))]))
            ","
            («term_∧_»
             (Term.app
              `Fermat42
              [(Term.proj `s "." (fieldIdx "1"))
               (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
               (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])
             "∧"
             («term_=_»
              `n
              "="
              (Term.app `Int.natAbs [(Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))]))))
           "}"))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`S_nonempty []]
          [(Term.typeSpec ":" `S.nonempty)]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.use "use" [(Term.app `Int.natAbs [`c])]) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_set_of_eq)] "]") []) [])
              (group
               (Tactic.use "use" [(Term.anonymousCtor "⟨" [`a "," (Term.anonymousCtor "⟨" [`b "," `c] "⟩")] "⟩")])
               [])
              (group (Tactic.tauto "tauto" []) [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl (Term.letIdDecl `m [(Term.typeSpec ":" (termℕ "ℕ"))] ":=" (Term.app `Nat.findₓ [`S_nonempty]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`m_mem []]
          [(Term.typeSpec ":" (Init.Core.«term_∈_» `m " ∈ " `S))]
          ":="
          (Term.app `Nat.find_specₓ [`S_nonempty]))))
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `m_mem)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s0)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs0)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs1)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.use
        "use"
        [(Term.proj `s0 "." (fieldIdx "1"))
         ","
         (Term.proj (Term.proj `s0 "." (fieldIdx "2")) "." (fieldIdx "1"))
         ","
         (Term.proj (Term.proj `s0 "." (fieldIdx "2")) "." (fieldIdx "2"))
         ","
         `hs0])
       [])
      (group (Tactic.intro "intro" [`a1 `b1 `c1 `h1]) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hs1)] "]") []) [])
      (group (Tactic.apply "apply" `Nat.find_min'ₓ) [])
      (group (Tactic.use "use" [(Term.anonymousCtor "⟨" [`a1 "," (Term.anonymousCtor "⟨" [`b1 "," `c1] "⟩")] "⟩")]) [])
      (group (Tactic.tauto "tauto" []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tauto "tauto" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tauto', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.use "use" [(Term.anonymousCtor "⟨" [`a1 "," (Term.anonymousCtor "⟨" [`b1 "," `c1] "⟩")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.use', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`a1 "," (Term.anonymousCtor "⟨" [`b1 "," `c1] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b1 "," `c1] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `Nat.find_min'ₓ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nat.find_min'ₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `hs1)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`a1 `b1 `c1 `h1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.use
   "use"
   [(Term.proj `s0 "." (fieldIdx "1"))
    ","
    (Term.proj (Term.proj `s0 "." (fieldIdx "2")) "." (fieldIdx "1"))
    ","
    (Term.proj (Term.proj `s0 "." (fieldIdx "2")) "." (fieldIdx "2"))
    ","
    `hs0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.use', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `s0 "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s0 "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `s0 "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s0 "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `s0 "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] `m_mem)]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s0)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs0)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs1)]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m_mem
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`m_mem []]
     [(Term.typeSpec ":" (Init.Core.«term_∈_» `m " ∈ " `S))]
     ":="
     (Term.app `Nat.find_specₓ [`S_nonempty]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.find_specₓ [`S_nonempty])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.find_specₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» `m " ∈ " `S)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl (Term.letIdDecl `m [(Term.typeSpec ":" (termℕ "ℕ"))] ":=" (Term.app `Nat.findₓ [`S_nonempty]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.findₓ [`S_nonempty])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.findₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`S_nonempty []]
     [(Term.typeSpec ":" `S.nonempty)]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.use "use" [(Term.app `Int.natAbs [`c])]) [])
         (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_set_of_eq)] "]") []) [])
         (group (Tactic.use "use" [(Term.anonymousCtor "⟨" [`a "," (Term.anonymousCtor "⟨" [`b "," `c] "⟩")] "⟩")]) [])
         (group (Tactic.tauto "tauto" []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.use "use" [(Term.app `Int.natAbs [`c])]) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_set_of_eq)] "]") []) [])
      (group (Tactic.use "use" [(Term.anonymousCtor "⟨" [`a "," (Term.anonymousCtor "⟨" [`b "," `c] "⟩")] "⟩")]) [])
      (group (Tactic.tauto "tauto" []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tauto "tauto" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tauto', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.use "use" [(Term.anonymousCtor "⟨" [`a "," (Term.anonymousCtor "⟨" [`b "," `c] "⟩")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.use', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`a "," (Term.anonymousCtor "⟨" [`b "," `c] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," `c] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_set_of_eq)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.use "use" [(Term.app `Int.natAbs [`c])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.use', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Int.natAbs [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Int.natAbs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S.nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `S
     [(Term.typeSpec ":" (Term.app `Set [(termℕ "ℕ")]))]
     ":="
     (Set.«term{_|_}»
      "{"
      `n
      "|"
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `s)]
         [":" («term_×_» (termℤ "ℤ") "×" («term_×_» (termℤ "ℤ") "×" (termℤ "ℤ")))]))
       ","
       («term_∧_»
        (Term.app
         `Fermat42
         [(Term.proj `s "." (fieldIdx "1"))
          (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
          (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])
        "∧"
        («term_=_» `n "=" (Term.app `Int.natAbs [(Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))]))))
      "}"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `n
   "|"
   («term∃_,_»
    "∃"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `s)]
      [":" («term_×_» (termℤ "ℤ") "×" («term_×_» (termℤ "ℤ") "×" (termℤ "ℤ")))]))
    ","
    («term_∧_»
     (Term.app
      `Fermat42
      [(Term.proj `s "." (fieldIdx "1"))
       (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
       (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])
     "∧"
     («term_=_» `n "=" (Term.app `Int.natAbs [(Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))]))))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `s)]
     [":" («term_×_» (termℤ "ℤ") "×" («term_×_» (termℤ "ℤ") "×" (termℤ "ℤ")))]))
   ","
   («term_∧_»
    (Term.app
     `Fermat42
     [(Term.proj `s "." (fieldIdx "1"))
      (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
      (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])
    "∧"
    («term_=_» `n "=" (Term.app `Int.natAbs [(Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   (Term.app
    `Fermat42
    [(Term.proj `s "." (fieldIdx "1"))
     (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
     (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])
   "∧"
   («term_=_» `n "=" (Term.app `Int.natAbs [(Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `n "=" (Term.app `Int.natAbs [(Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Int.natAbs [(Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Int.natAbs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  (Term.app
   `Fermat42
   [(Term.proj `s "." (fieldIdx "1"))
    (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
    (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fermat42
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_×_» (termℤ "ℤ") "×" («term_×_» (termℤ "ℤ") "×" (termℤ "ℤ")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_×_» (termℤ "ℤ") "×" (termℤ "ℤ"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℤ "ℤ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  (termℤ "ℤ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  (termℤ "ℤ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
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
/-- if we have a solution to `a ^ 4 + b ^ 4 = c ^ 2` then there must be a minimal one. -/
  theorem
    exists_minimal
    { a b c : ℤ } ( h : Fermat42 a b c ) : ∃ a0 b0 c0 , minimal a0 b0 c0
    :=
      by
        let S : Set ℕ := { n | ∃ s : ℤ × ℤ × ℤ , Fermat42 s . 1 s . 2 . 1 s . 2 . 2 ∧ n = Int.natAbs s . 2 . 2 }
          have S_nonempty : S.nonempty := by use Int.natAbs c rw [ Set.mem_set_of_eq ] use ⟨ a , ⟨ b , c ⟩ ⟩ tauto
          let m : ℕ := Nat.findₓ S_nonempty
          have m_mem : m ∈ S := Nat.find_specₓ S_nonempty
          rcases m_mem with ⟨ s0 , hs0 , hs1 ⟩
          use s0 . 1 , s0 . 2 . 1 , s0 . 2 . 2 , hs0
          intro a1 b1 c1 h1
          rw [ ← hs1 ]
          apply Nat.find_min'ₓ
          use ⟨ a1 , ⟨ b1 , c1 ⟩ ⟩
          tauto

/--  a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` must have `a` and `b` coprime. -/
theorem coprime_of_minimal {a b c : ℤ} (h : minimal a b c) : IsCoprime a b := by
  apply int.gcd_eq_one_iff_coprime.mp
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := nat.prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a1, rfl⟩ := int.coe_nat_dvd_left.mpr hpa
  obtain ⟨b1, rfl⟩ := int.coe_nat_dvd_left.mpr hpb
  have hpc : ((p : ℤ)^2) ∣ c := by
    apply
      (Int.pow_dvd_pow_iff
          (by
            decide : 0 < 2)).mp
    rw [← h.1.2.2]
    apply Dvd.intro ((a1^4)+b1^4)
    ring
  obtain ⟨c1, rfl⟩ := hpc
  have hf : Fermat42 a1 b1 c1
  exact (Fermat42.mul (int.coe_nat_ne_zero.mpr (Nat.Prime.ne_zero hp))).mpr h.1
  apply Nat.le_lt_antisymmₓ (h.2 _ _ _ hf)
  rw [Int.nat_abs_mul, lt_mul_iff_one_lt_left, Int.nat_abs_pow, Int.nat_abs_of_nat]
  ·
    exact
      Nat.one_lt_pow _ _
        (show 0 < 2 from by
          decide)
        (Nat.Prime.one_lt hp)
  ·
    exact Nat.pos_of_ne_zeroₓ (Int.nat_abs_ne_zero_of_ne_zero (ne_zero hf))

/--  We can swap `a` and `b` in a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2`. -/
theorem minimal_comm {a b c : ℤ} : minimal a b c → minimal b a c := fun ⟨h1, h2⟩ => ⟨Fermat42.comm.mp h1, h2⟩

/--  We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has positive `c`. -/
theorem neg_of_minimal {a b c : ℤ} : minimal a b c → minimal a b (-c) := by
  rintro ⟨⟨ha, hb, heq⟩, h2⟩
  constructor
  ·
    apply And.intro ha (And.intro hb _)
    rw [HEq]
    exact (neg_sq c).symm
  rwa [Int.nat_abs_neg c]

/--  We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has `a` odd. -/
theorem exists_odd_minimal {a b c : ℤ} (h : Fermat42 a b c) : ∃ a0 b0 c0, minimal a0 b0 c0 ∧ a0 % 2 = 1 := by
  obtain ⟨a0, b0, c0, hf⟩ := exists_minimal h
  cases' Int.mod_two_eq_zero_or_one a0 with hap hap
  ·
    cases' Int.mod_two_eq_zero_or_one b0 with hbp hbp
    ·
      exfalso
      have h1 : 2 ∣ (Int.gcdₓ a0 b0 : ℤ) := by
        exact Int.dvd_gcd (Int.dvd_of_mod_eq_zero hap) (Int.dvd_of_mod_eq_zero hbp)
      rw [int.gcd_eq_one_iff_coprime.mpr (coprime_of_minimal hf)] at h1
      revert h1
      norm_num
    ·
      exact ⟨b0, ⟨a0, ⟨c0, minimal_comm hf, hbp⟩⟩⟩
  exact ⟨a0, ⟨b0, ⟨c0, hf, hap⟩⟩⟩

/--  We can assume that a minimal solution to `a ^ 4 + b ^ 4 = c ^ 2` has
`a` odd and `c` positive. -/
theorem exists_pos_odd_minimal {a b c : ℤ} (h : Fermat42 a b c) : ∃ a0 b0 c0, minimal a0 b0 c0 ∧ a0 % 2 = 1 ∧ 0 < c0 :=
  by
  obtain ⟨a0, b0, c0, hf, hc⟩ := exists_odd_minimal h
  rcases lt_trichotomyₓ 0 c0 with (h1 | rfl | h1)
  ·
    use a0, b0, c0
    tauto
  ·
    exfalso
    exact ne_zero hf.1 rfl
  ·
    use a0, b0, -c0, neg_of_minimal hf, hc
    exact neg_pos.mpr h1

end Fermat42

theorem Int.coprime_of_sq_sum {r s : ℤ} (h2 : IsCoprime s r) : IsCoprime ((r^2)+s^2) r := by
  rw [sq, sq]
  exact (IsCoprime.mul_left h2 h2).mul_add_left_left r

theorem Int.coprime_of_sq_sum' {r s : ℤ} (h : IsCoprime r s) : IsCoprime ((r^2)+s^2) (r*s) := by
  apply IsCoprime.mul_right (Int.coprime_of_sq_sum (is_coprime_comm.mp h))
  rw [add_commₓ]
  apply Int.coprime_of_sq_sum h

namespace Fermat42

theorem not_minimal {a b c : ℤ} (h : minimal a b c) (ha2 : a % 2 = 1) (hc : 0 < c) : False := by
  have ht : PythagoreanTriple (a^2) (b^2) c := by
    calc (((a^2)*a^2)+(b^2)*b^2) = (a^4)+b^4 := by
      ring _ = (c^2) := by
      rw [h.1.2.2]_ = c*c := by
      rw [sq]
  have h2 : Int.gcdₓ (a^2) (b^2) = 1 := int.gcd_eq_one_iff_coprime.mpr (coprime_of_minimal h).pow
  have ha22 : (a^2) % 2 = 1 := by
    rw [sq, Int.mul_mod, ha2]
    norm_num
  obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ := PythagoreanTriple.coprime_classification' ht h2 ha22 hc
  have htt : PythagoreanTriple a n m := by
    delta' PythagoreanTriple
    rw [← sq, ← sq, ← sq]
    exact add_eq_of_eq_sub ht1
  have h3 : Int.gcdₓ a n = 1 := by
    apply int.gcd_eq_one_iff_coprime.mpr
    apply @IsCoprime.of_mul_left_left _ _ _ a
    rw [← sq, ht1,
      (by
        ring : (m^2) - (n^2) = (m^2)+(-n)*n)]
    exact (int.gcd_eq_one_iff_coprime.mp ht4).pow_left.add_mul_right_left (-n)
  have hb20 : (b^2) ≠ 0 := mt pow_eq_zero h.1.2.1
  have h4 : 0 < m := by
    apply lt_of_le_of_neₓ ht6
    rintro rfl
    revert hb20
    rw [ht2]
    simp
  obtain ⟨r, s, htt1, htt2, htt3, htt4, htt5, htt6⟩ := PythagoreanTriple.coprime_classification' htt h3 ha2 h4
  have hcp : Int.gcdₓ m (r*s) = 1 := by
    rw [htt3]
    exact int.gcd_eq_one_iff_coprime.mpr (Int.coprime_of_sq_sum' (int.gcd_eq_one_iff_coprime.mp htt4))
  have hb2 : 2 ∣ b := by
    apply
      @Int.Prime.dvd_pow' _ 2 _
        (by
          norm_num : Nat.Prime 2)
    rw [ht2, mul_assocₓ]
    exact dvd_mul_right 2 (m*n)
  cases' hb2 with b' hb2'
  have hs : (b'^2) = m*r*s := by
    apply
      (mul_right_inj'
          (by
            norm_num : (4 : ℤ) ≠ 0)).mp
    calc (4*b'^2) = (2*b')*2*b' := by
      ring _ = (2*m)*(2*r)*s := by
      rw [← hb2', ← sq, ht2, htt2]_ = 4*m*r*s := by
      ring
  have hrsz : (r*s) ≠ 0 := by
    by_contra hrsz
    revert hb20
    rw [ht2, htt2, mul_assocₓ, @mul_assocₓ _ _ _ r s, hrsz]
    simp
  have h2b0 : b' ≠ 0 := by
    apply
      ne_zero_pow
        (by
          decide : 2 ≠ 0)
    rw [hs]
    apply mul_ne_zero
    ·
      exact ne_of_gtₓ h4
    ·
      exact hrsz
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one hcp hs.symm
  have hi' : ¬m = -(i^2) := by
    by_contra h1
    have hit : -(i^2) ≤ 0
    apply neg_nonpos.mpr (sq_nonneg i)
    rw [← h1] at hit
    apply absurd h4 (not_lt.mpr hit)
  replace hi : m = (i^2)
  ·
    apply Or.resolve_right hi hi'
  rw [mul_commₓ] at hs
  rw [Int.gcd_comm] at hcp
  obtain ⟨d, hd⟩ := Int.sq_of_gcd_eq_one hcp hs.symm
  have hd' : ¬(r*s) = -(d^2) := by
    by_contra h1
    rw [h1] at hs
    have h2 : (b'^2) ≤ 0 := by
      rw [hs,
        (by
          ring : ((-(d^2))*m) = -(d^2)*m)]
      exact neg_nonpos.mpr ((zero_le_mul_right h4).mpr (sq_nonneg d))
    have h2' : 0 ≤ (b'^2) := by
      apply sq_nonneg b'
    exact absurd (lt_of_le_of_neₓ h2' (Ne.symm (pow_ne_zero _ h2b0))) (not_lt.mpr h2)
  replace hd : (r*s) = (d^2)
  ·
    apply Or.resolve_right hd hd'
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one htt4 hd
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0,
      zero_pow
        (by
          decide : 0 < 2),
      neg_zero, or_selfₓ] at hj
    apply left_ne_zero_of_mul hrsz hj
  rw [mul_commₓ] at hd
  rw [Int.gcd_comm] at htt4
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one htt4 hd
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0,
      zero_pow
        (by
          decide : 0 < 2),
      neg_zero, or_selfₓ] at hk
    apply right_ne_zero_of_mul hrsz hk
  have hj2 : (r^2) = (j^4) := by
    cases' hj with hjp hjp <;>
      ·
        rw [hjp]
        ring
  have hk2 : (s^2) = (k^4) := by
    cases' hk with hkp hkp <;>
      ·
        rw [hkp]
        ring
  have hh : (i^2) = (j^4)+k^4 := by
    rw [← hi, htt3, hj2, hk2]
  have hn : n ≠ 0 := by
    rw [ht2] at hb20
    apply right_ne_zero_of_mul hb20
  have hic : Int.natAbs i < Int.natAbs c := by
    apply int.coe_nat_lt.mp
    rw [← Int.eq_nat_abs_of_zero_le (le_of_ltₓ hc)]
    apply gt_of_gt_of_geₓ _ (Int.abs_le_self_sq i)
    rw [← hi, ht3]
    apply gt_of_gt_of_geₓ _ (Int.le_self_sq m)
    exact lt_add_of_pos_right (m^2) (sq_pos_of_ne_zero n hn)
  have hic' : Int.natAbs c ≤ Int.natAbs i := by
    apply h.2 j k i
    exact ⟨hj0, hk0, hh.symm⟩
  apply absurd (not_le_of_lt hic) (not_not.mpr hic')

end Fermat42

theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : ((a^4)+b^4) ≠ (c^2) := by
  intro h
  obtain ⟨a0, b0, c0, ⟨hf, h2, hp⟩⟩ := Fermat42.exists_pos_odd_minimal (And.intro ha (And.intro hb h))
  apply Fermat42.not_minimal hf h2 hp

theorem not_fermat_4 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : ((a^4)+b^4) ≠ (c^4) := by
  intro heq
  apply @not_fermat_42 _ _ (c^2) ha hb
  rw [HEq]
  ring

