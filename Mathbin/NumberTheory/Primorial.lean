import Mathbin.Tactic.RingExp
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Nat.Choose.Sum

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notations

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/


open Finset

open Nat

open_locale BigOperators Nat

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " The primorial `n#` of `n` is the product of the primes less than or equal to `n`.\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `primorial [])
  (Command.optDeclSig [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")] [(Term.typeSpec ":" (termℕ "ℕ"))])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
    " in "
    (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
    ", "
    `p)
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
   " in "
   (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
   ", "
   `p)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `range [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `prime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
    -/
  def primorial ( n : ℕ ) : ℕ := ∏ p in filter prime range n + 1 , p

local notation x "#" => primorial x

theorem primorial_succ {n : ℕ} (n_big : 1 < n) (r : n % 2 = 1) : (n+1)# = n# := by
  have not_prime : ¬prime (n+1) := by
    intro is_prime
    cases' prime.eq_two_or_odd is_prime with _ n_even
    ·
      linarith
    ·
      exfalso
      rw [← not_even_iff] at n_even r
      have e : Even ((n+1) - n) := (even_sub (lt_add_one n).le).2 (iff_of_false n_even r)
      simp only [add_tsub_cancel_left, not_even_one] at e
      exact e
  apply Finset.prod_congr
  ·
    rw [@range_succ (n+1), filter_insert, if_neg not_prime]
  ·
    exact fun _ _ => rfl

theorem dvd_choose_of_middling_prime (p : ℕ) (is_prime : prime p) (m : ℕ) (p_big : (m+1) < p) (p_small : p ≤ (2*m)+1) :
    p ∣ choose ((2*m)+1) (m+1) := by
  have m_size : (m+1) ≤ (2*m)+1 := le_of_ltₓ (lt_of_lt_of_leₓ p_big p_small)
  have s : ¬p ∣ (m+1)! := by
    intro p_div_fact
    have p_le_succ_m : p ≤ m+1 := (prime.dvd_factorial is_prime).mp p_div_fact
    linarith
  have t : ¬p ∣ (((2*m)+1) - m+1)! := by
    intro p_div_fact
    have p_small : p ≤ ((2*m)+1) - m+1 := (prime.dvd_factorial is_prime).mp p_div_fact
    linarith
  have expanded : ((choose ((2*m)+1) (m+1)*(m+1)!)*(((2*m)+1) - m+1)!) = ((2*m)+1)! :=
    @choose_mul_factorial_mul_factorial ((2*m)+1) (m+1) m_size
  have p_div_big_fact : p ∣ ((2*m)+1)! := (prime.dvd_factorial is_prime).mpr p_small
  rw [← expanded, mul_assocₓ] at p_div_big_fact
  obtain p_div_choose | p_div_facts : p ∣ choose ((2*m)+1) (m+1) ∨ p ∣ _ !*_ ! :=
    (prime.dvd_mul is_prime).1 p_div_big_fact
  ·
    exact p_div_choose
  cases (prime.dvd_mul is_prime).1 p_div_facts
  cc
  cc

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `prod_primes_dvd [])
  (Command.declSig
   [(Term.implicitBinder "{" [`s] [":" (Term.app `Finset [(termℕ "ℕ")])] "}")]
   (Term.typeSpec
    ":"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])
      (Term.simpleBinder
       [`h]
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          []
          ","
          (Mathlib.ExtendedBinder.«term∀___,_»
           "∀"
           `a
           («binderTerm∈_» "∈" `s)
           ","
           (Term.forall "∀" [] "," (Term.app `prime [`a])))))])
      (Term.simpleBinder
       [`div]
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          []
          ","
          (Mathlib.ExtendedBinder.«term∀___,_»
           "∀"
           `a
           («binderTerm∈_» "∈" `s)
           ","
           (Term.forall "∀" [] "," (Init.Core.«term_∣_» `a " ∣ " `n)))))])]
     ","
     (Init.Core.«term_∣_»
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
       " in "
       `s
       ", "
       `p)
      " ∣ "
      `n))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" (Term.app `Finset.induction_on [`s])) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`a `s `a_not_in_s `induct `n `primes `divs]) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Finset.prod_insert [`a_not_in_s]))] "]")
              [])
             [])
            (group
             (Tactic.obtain
              "obtain"
              [(Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                  "⟩")])]
              [":" (Init.Core.«term_∣_» `a " ∣ " `n)]
              [])
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.exact "exact" (Term.app `divs [`a (Term.app `Finset.mem_insert_self [`a `s])])) [])])))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`step []]
                [(Term.typeSpec
                  ":"
                  (Init.Core.«term_∣_»
                   (Algebra.BigOperators.Basic.«term∏_in_,_»
                    "∏"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
                    " in "
                    `s
                    ", "
                    `p)
                   " ∣ "
                   `k))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.apply "apply" (Term.app `induct [`k])) [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.intro "intro" [`b `b_in_s]) [])
                         (group
                          (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                          [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.intro "intro" [`b `b_in_s]) [])
                         (group
                          (Tactic.tacticHave_
                           "have"
                           (Term.haveDecl
                            (Term.haveIdDecl
                             [`b_div_n []]
                             []
                             ":="
                             (Term.byTactic
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group
                                  (Tactic.exact
                                   "exact"
                                   (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                                  [])]))))))
                          [])
                         (group
                          (Tactic.tacticHave_
                           "have"
                           (Term.haveDecl
                            (Term.haveIdDecl
                             [`a_prime []]
                             [(Term.typeSpec ":" (Term.app `prime [`a]))]
                             ":="
                             (Term.byTactic
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group
                                  (Tactic.exact
                                   "exact"
                                   (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])]))
                                  [])]))))))
                          [])
                         (group
                          (Tactic.tacticHave_
                           "have"
                           (Term.haveDecl
                            (Term.haveIdDecl
                             [`b_prime []]
                             [(Term.typeSpec ":" (Term.app `prime [`b]))]
                             ":="
                             (Term.byTactic
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group
                                  (Tactic.exact
                                   "exact"
                                   (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                                  [])]))))))
                          [])
                         (group
                          (Tactic.obtain
                           "obtain"
                           [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b_div_a) "|" (Tactic.rcasesPat.one `b_div_k)])]
                           [":" («term_∨_» (Init.Core.«term_∣_» `b " ∣ " `a) "∨" (Init.Core.«term_∣_» `b " ∣ " `k))]
                           [])
                          [])
                         (group
                          (Tactic.exact
                           "exact"
                           (Term.app (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp) [`b_div_n]))
                          [])
                         (group
                          (Tactic.«tactic·._»
                           "·"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group (tacticExfalso "exfalso") [])
                              (group
                               (Tactic.tacticHave_
                                "have"
                                (Term.haveDecl
                                 (Term.haveIdDecl
                                  [`b_eq_a []]
                                  [(Term.typeSpec ":" («term_=_» `b "=" `a))]
                                  ":="
                                  (Term.byTactic
                                   "by"
                                   (Tactic.tacticSeq
                                    (Tactic.tacticSeq1Indented
                                     [(group
                                       (Tactic.cases'
                                        "cases'"
                                        [(Tactic.casesTarget
                                          []
                                          (Term.app
                                           (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1"))
                                           [`b_div_a]))]
                                        []
                                        ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
                                       [])
                                      (group
                                       (Tactic.«tactic·._»
                                        "·"
                                        (Tactic.tacticSeq
                                         (Tactic.tacticSeq1Indented
                                          [(group (Tactic.subst "subst" [`b_eq_1]) [])
                                           (group (tacticExfalso "exfalso") [])
                                           (group
                                            (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl]))
                                            [])])))
                                       [])
                                      (group
                                       (Tactic.«tactic·._»
                                        "·"
                                        (Tactic.tacticSeq
                                         (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
                                       [])]))))))
                               [])
                              (group (Tactic.subst "subst" [`b_eq_a]) [])
                              (group (Tactic.exact "exact" (Term.app `a_not_in_s [`b_in_s])) [])])))
                          [])
                         (group
                          (Tactic.«tactic·._»
                           "·"
                           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_div_k) [])])))
                          [])])))
                     [])]))))))
             [])
            (group (Tactic.exact "exact" (Term.app `mul_dvd_mul_left [`a `step])) [])])))
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
     [(group (Tactic.apply "apply" (Term.app `Finset.induction_on [`s])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`a `s `a_not_in_s `induct `n `primes `divs]) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Finset.prod_insert [`a_not_in_s]))] "]")
             [])
            [])
           (group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                 "⟩")])]
             [":" (Init.Core.«term_∣_» `a " ∣ " `n)]
             [])
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.exact "exact" (Term.app `divs [`a (Term.app `Finset.mem_insert_self [`a `s])])) [])])))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`step []]
               [(Term.typeSpec
                 ":"
                 (Init.Core.«term_∣_»
                  (Algebra.BigOperators.Basic.«term∏_in_,_»
                   "∏"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
                   " in "
                   `s
                   ", "
                   `p)
                  " ∣ "
                  `k))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.apply "apply" (Term.app `induct [`k])) [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.intro "intro" [`b `b_in_s]) [])
                        (group
                         (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                         [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.intro "intro" [`b `b_in_s]) [])
                        (group
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`b_div_n []]
                            []
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.exact
                                  "exact"
                                  (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                                 [])]))))))
                         [])
                        (group
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`a_prime []]
                            [(Term.typeSpec ":" (Term.app `prime [`a]))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.exact
                                  "exact"
                                  (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])]))
                                 [])]))))))
                         [])
                        (group
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`b_prime []]
                            [(Term.typeSpec ":" (Term.app `prime [`b]))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.exact
                                  "exact"
                                  (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                                 [])]))))))
                         [])
                        (group
                         (Tactic.obtain
                          "obtain"
                          [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b_div_a) "|" (Tactic.rcasesPat.one `b_div_k)])]
                          [":" («term_∨_» (Init.Core.«term_∣_» `b " ∣ " `a) "∨" (Init.Core.«term_∣_» `b " ∣ " `k))]
                          [])
                         [])
                        (group
                         (Tactic.exact
                          "exact"
                          (Term.app (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp) [`b_div_n]))
                         [])
                        (group
                         (Tactic.«tactic·._»
                          "·"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group (tacticExfalso "exfalso") [])
                             (group
                              (Tactic.tacticHave_
                               "have"
                               (Term.haveDecl
                                (Term.haveIdDecl
                                 [`b_eq_a []]
                                 [(Term.typeSpec ":" («term_=_» `b "=" `a))]
                                 ":="
                                 (Term.byTactic
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(group
                                      (Tactic.cases'
                                       "cases'"
                                       [(Tactic.casesTarget
                                         []
                                         (Term.app
                                          (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1"))
                                          [`b_div_a]))]
                                       []
                                       ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
                                      [])
                                     (group
                                      (Tactic.«tactic·._»
                                       "·"
                                       (Tactic.tacticSeq
                                        (Tactic.tacticSeq1Indented
                                         [(group (Tactic.subst "subst" [`b_eq_1]) [])
                                          (group (tacticExfalso "exfalso") [])
                                          (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
                                      [])
                                     (group
                                      (Tactic.«tactic·._»
                                       "·"
                                       (Tactic.tacticSeq
                                        (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
                                      [])]))))))
                              [])
                             (group (Tactic.subst "subst" [`b_eq_a]) [])
                             (group (Tactic.exact "exact" (Term.app `a_not_in_s [`b_in_s])) [])])))
                         [])
                        (group
                         (Tactic.«tactic·._»
                          "·"
                          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_div_k) [])])))
                         [])])))
                    [])]))))))
            [])
           (group (Tactic.exact "exact" (Term.app `mul_dvd_mul_left [`a `step])) [])])))
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
     [(group (Tactic.intro "intro" [`a `s `a_not_in_s `induct `n `primes `divs]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Finset.prod_insert [`a_not_in_s]))] "]")
        [])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
            "⟩")])]
        [":" (Init.Core.«term_∣_» `a " ∣ " `n)]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.exact "exact" (Term.app `divs [`a (Term.app `Finset.mem_insert_self [`a `s])])) [])])))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`step []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∣_»
             (Algebra.BigOperators.Basic.«term∏_in_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
              " in "
              `s
              ", "
              `p)
             " ∣ "
             `k))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.apply "apply" (Term.app `induct [`k])) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`b `b_in_s]) [])
                   (group
                    (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`b `b_in_s]) [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`b_div_n []]
                       []
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.exact "exact" (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                            [])]))))))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`a_prime []]
                       [(Term.typeSpec ":" (Term.app `prime [`a]))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.exact "exact" (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])]))
                            [])]))))))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`b_prime []]
                       [(Term.typeSpec ":" (Term.app `prime [`b]))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.exact
                             "exact"
                             (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                            [])]))))))
                    [])
                   (group
                    (Tactic.obtain
                     "obtain"
                     [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b_div_a) "|" (Tactic.rcasesPat.one `b_div_k)])]
                     [":" («term_∨_» (Init.Core.«term_∣_» `b " ∣ " `a) "∨" (Init.Core.«term_∣_» `b " ∣ " `k))]
                     [])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp) [`b_div_n]))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (tacticExfalso "exfalso") [])
                        (group
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`b_eq_a []]
                            [(Term.typeSpec ":" («term_=_» `b "=" `a))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.cases'
                                  "cases'"
                                  [(Tactic.casesTarget
                                    []
                                    (Term.app
                                     (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1"))
                                     [`b_div_a]))]
                                  []
                                  ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
                                 [])
                                (group
                                 (Tactic.«tactic·._»
                                  "·"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(group (Tactic.subst "subst" [`b_eq_1]) [])
                                     (group (tacticExfalso "exfalso") [])
                                     (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
                                 [])
                                (group
                                 (Tactic.«tactic·._»
                                  "·"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
                                 [])]))))))
                         [])
                        (group (Tactic.subst "subst" [`b_eq_a]) [])
                        (group (Tactic.exact "exact" (Term.app `a_not_in_s [`b_in_s])) [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_div_k) [])])))
                    [])])))
               [])]))))))
       [])
      (group (Tactic.exact "exact" (Term.app `mul_dvd_mul_left [`a `step])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `mul_dvd_mul_left [`a `step]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_dvd_mul_left [`a `step])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `step
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_dvd_mul_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`step []]
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∣_»
        (Algebra.BigOperators.Basic.«term∏_in_,_»
         "∏"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
         " in "
         `s
         ", "
         `p)
        " ∣ "
        `k))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.apply "apply" (Term.app `induct [`k])) [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`b `b_in_s]) [])
              (group
               (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
               [])])))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`b `b_in_s]) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`b_div_n []]
                  []
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.exact "exact" (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                       [])]))))))
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`a_prime []]
                  [(Term.typeSpec ":" (Term.app `prime [`a]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.exact "exact" (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])]))
                       [])]))))))
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`b_prime []]
                  [(Term.typeSpec ":" (Term.app `prime [`b]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                       [])]))))))
               [])
              (group
               (Tactic.obtain
                "obtain"
                [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b_div_a) "|" (Tactic.rcasesPat.one `b_div_k)])]
                [":" («term_∨_» (Init.Core.«term_∣_» `b " ∣ " `a) "∨" (Init.Core.«term_∣_» `b " ∣ " `k))]
                [])
               [])
              (group
               (Tactic.exact "exact" (Term.app (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp) [`b_div_n]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (tacticExfalso "exfalso") [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`b_eq_a []]
                       [(Term.typeSpec ":" («term_=_» `b "=" `a))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.cases'
                             "cases'"
                             [(Tactic.casesTarget
                               []
                               (Term.app
                                (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1"))
                                [`b_div_a]))]
                             []
                             ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
                            [])
                           (group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group (Tactic.subst "subst" [`b_eq_1]) [])
                                (group (tacticExfalso "exfalso") [])
                                (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
                            [])
                           (group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
                            [])]))))))
                    [])
                   (group (Tactic.subst "subst" [`b_eq_a]) [])
                   (group (Tactic.exact "exact" (Term.app `a_not_in_s [`b_in_s])) [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_div_k) [])])))
               [])])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" (Term.app `induct [`k])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`b `b_in_s]) [])
           (group (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`b `b_in_s]) [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`b_div_n []]
               []
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.exact "exact" (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`a_prime []]
               [(Term.typeSpec ":" (Term.app `prime [`a]))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.exact "exact" (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])]))
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`b_prime []]
               [(Term.typeSpec ":" (Term.app `prime [`b]))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
                    [])]))))))
            [])
           (group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b_div_a) "|" (Tactic.rcasesPat.one `b_div_k)])]
             [":" («term_∨_» (Init.Core.«term_∣_» `b " ∣ " `a) "∨" (Init.Core.«term_∣_» `b " ∣ " `k))]
             [])
            [])
           (group
            (Tactic.exact "exact" (Term.app (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp) [`b_div_n]))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (tacticExfalso "exfalso") [])
                (group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`b_eq_a []]
                    [(Term.typeSpec ":" («term_=_» `b "=" `a))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.cases'
                          "cases'"
                          [(Tactic.casesTarget
                            []
                            (Term.app (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1")) [`b_div_a]))]
                          []
                          ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
                         [])
                        (group
                         (Tactic.«tactic·._»
                          "·"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group (Tactic.subst "subst" [`b_eq_1]) [])
                             (group (tacticExfalso "exfalso") [])
                             (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
                         [])
                        (group
                         (Tactic.«tactic·._»
                          "·"
                          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
                         [])]))))))
                 [])
                (group (Tactic.subst "subst" [`b_eq_a]) [])
                (group (Tactic.exact "exact" (Term.app `a_not_in_s [`b_in_s])) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_div_k) [])])))
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
     [(group (Tactic.intro "intro" [`b `b_in_s]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`b_div_n []]
          []
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.exact "exact" (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`a_prime []]
          [(Term.typeSpec ":" (Term.app `prime [`a]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.exact "exact" (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`b_prime []]
          [(Term.typeSpec ":" (Term.app `prime [`b]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
               [])]))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b_div_a) "|" (Tactic.rcasesPat.one `b_div_k)])]
        [":" («term_∨_» (Init.Core.«term_∣_» `b " ∣ " `a) "∨" (Init.Core.«term_∣_» `b " ∣ " `k))]
        [])
       [])
      (group (Tactic.exact "exact" (Term.app (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp) [`b_div_n])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (tacticExfalso "exfalso") [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`b_eq_a []]
               [(Term.typeSpec ":" («term_=_» `b "=" `a))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.cases'
                     "cases'"
                     [(Tactic.casesTarget
                       []
                       (Term.app (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1")) [`b_div_a]))]
                     []
                     ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.subst "subst" [`b_eq_1]) [])
                        (group (tacticExfalso "exfalso") [])
                        (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
                    [])]))))))
            [])
           (group (Tactic.subst "subst" [`b_eq_a]) [])
           (group (Tactic.exact "exact" (Term.app `a_not_in_s [`b_in_s])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_div_k) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_div_k) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `b_div_k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_div_k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (tacticExfalso "exfalso") [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`b_eq_a []]
          [(Term.typeSpec ":" («term_=_» `b "=" `a))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.cases'
                "cases'"
                [(Tactic.casesTarget
                  []
                  (Term.app (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1")) [`b_div_a]))]
                []
                ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.subst "subst" [`b_eq_1]) [])
                   (group (tacticExfalso "exfalso") [])
                   (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
               [])]))))))
       [])
      (group (Tactic.subst "subst" [`b_eq_a]) [])
      (group (Tactic.exact "exact" (Term.app `a_not_in_s [`b_in_s])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `a_not_in_s [`b_in_s]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `a_not_in_s [`b_in_s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_in_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `a_not_in_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.subst "subst" [`b_eq_a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_eq_a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`b_eq_a []]
     [(Term.typeSpec ":" («term_=_» `b "=" `a))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.cases'
           "cases'"
           [(Tactic.casesTarget
             []
             (Term.app (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1")) [`b_div_a]))]
           []
           ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.subst "subst" [`b_eq_1]) [])
              (group (tacticExfalso "exfalso") [])
              (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget
          []
          (Term.app (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1")) [`b_div_a]))]
        []
        ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.subst "subst" [`b_eq_1]) [])
           (group (tacticExfalso "exfalso") [])
           (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" `b_eq_a) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `b_eq_a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_eq_a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.subst "subst" [`b_eq_1]) [])
      (group (tacticExfalso "exfalso") [])
      (group (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `prime.ne_one [`b_prime `rfl]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `prime.ne_one [`b_prime `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b_prime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `prime.ne_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticExfalso "exfalso")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticExfalso', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.subst "subst" [`b_eq_1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_eq_1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases'
   "cases'"
   [(Tactic.casesTarget [] (Term.app (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1")) [`b_div_a]))]
   []
   ["with" [(Lean.binderIdent `b_eq_1) (Lean.binderIdent `b_eq_a)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1")) [`b_div_a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_div_a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `Nat.dvd_prime [`a_prime]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Nat.dvd_prime [`a_prime])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a_prime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.dvd_prime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.dvd_prime [`a_prime]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `b "=" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticExfalso "exfalso")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticExfalso', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.exact "exact" (Term.app (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp) [`b_div_n]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp) [`b_div_n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_div_n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `prime.dvd_mul [`b_prime]) "." `mp)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `prime.dvd_mul [`b_prime])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_prime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `prime.dvd_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `prime.dvd_mul [`b_prime]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b_div_a) "|" (Tactic.rcasesPat.one `b_div_k)])]
   [":" («term_∨_» (Init.Core.«term_∣_» `b " ∣ " `a) "∨" (Init.Core.«term_∣_» `b " ∣ " `k))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∨_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∨_» (Init.Core.«term_∣_» `b " ∣ " `a) "∨" (Init.Core.«term_∣_» `b " ∣ " `k))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∨_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∣_» `b " ∣ " `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
  (Init.Core.«term_∣_» `b " ∣ " `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 51, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 30, (some 30, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatMed', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`b_prime []]
     [(Term.typeSpec ":" (Term.app `prime [`b]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.mem_insert_of_mem [`b_in_s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_in_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.mem_insert_of_mem
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finset.mem_insert_of_mem [`b_in_s]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `primes
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `prime [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `prime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`a_prime []]
     [(Term.typeSpec ":" (Term.app `prime [`a]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.exact "exact" (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])])) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.exact "exact" (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `primes [`a (Term.app `Finset.mem_insert_self [`a `s])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.mem_insert_self [`a `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.mem_insert_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finset.mem_insert_self [`a `s]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `primes
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `prime [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `prime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`b_div_n []]
     []
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.exact "exact" (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.exact "exact" (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `divs [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.mem_insert_of_mem [`b_in_s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_in_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.mem_insert_of_mem
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finset.mem_insert_of_mem [`b_in_s]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `divs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`b `b_in_s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_in_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`b `b_in_s]) [])
      (group (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `primes [`b (Term.app `Finset.mem_insert_of_mem [`b_in_s])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.mem_insert_of_mem [`b_in_s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_in_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.mem_insert_of_mem
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finset.mem_insert_of_mem [`b_in_s]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `primes
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`b `b_in_s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b_in_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.app `induct [`k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `induct [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `induct
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∣_»
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
    " in "
    `s
    ", "
    `p)
   " ∣ "
   `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∣_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
   " in "
   `s
   ", "
   `p)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
  prod_primes_dvd
  { s : Finset ℕ } : ∀ n : ℕ h : ∀ , ∀ a ∈ s , ∀ , prime a div : ∀ , ∀ a ∈ s , ∀ , a ∣ n , ∏ p in s , p ∣ n
  :=
    by
      apply Finset.induction_on s
        · simp
        ·
          intro a s a_not_in_s induct n primes divs
            rw [ Finset.prod_insert a_not_in_s ]
            obtain ⟨ k , rfl ⟩ : a ∣ n
            · exact divs a Finset.mem_insert_self a s
            have
              step
                : ∏ p in s , p ∣ k
                :=
                by
                  apply induct k
                    · intro b b_in_s exact primes b Finset.mem_insert_of_mem b_in_s
                    ·
                      intro b b_in_s
                        have b_div_n := by exact divs b Finset.mem_insert_of_mem b_in_s
                        have a_prime : prime a := by exact primes a Finset.mem_insert_self a s
                        have b_prime : prime b := by exact primes b Finset.mem_insert_of_mem b_in_s
                        obtain b_div_a | b_div_k : b ∣ a ∨ b ∣ k
                        exact prime.dvd_mul b_prime . mp b_div_n
                        ·
                          exfalso
                            have
                              b_eq_a
                                : b = a
                                :=
                                by
                                  cases' Nat.dvd_prime a_prime . 1 b_div_a with b_eq_1 b_eq_a
                                    · subst b_eq_1 exfalso exact prime.ne_one b_prime rfl
                                    · exact b_eq_a
                            subst b_eq_a
                            exact a_not_in_s b_in_s
                        · exact b_div_k
            exact mul_dvd_mul_left a step

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `primorial_le_4_pow [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    (Term.forall
     "∀"
     [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
     ","
     («term_≤_» (NumberTheory.Primorial.«term_#» `n "#") "≤" («term_^_» (numLit "4") "^" `n)))))
  (Command.declValEqns
   (Term.matchAltsWhereDecls
    (Term.matchAlts
     [(Term.matchAlt "|" [(numLit "0")] "=>" (Term.app `le_reflₓ [(Term.hole "_")]))
      (Term.matchAlt "|" [(numLit "1")] "=>" (Term.app `le_of_inf_eq [`rfl]))
      (Term.matchAlt
       "|"
       [(Init.Logic.«term_+_» `n "+" (numLit "2"))]
       "=>"
       (Term.match
        "match"
        []
        [(Term.matchDiscr [] (Term.app `Nat.mod_two_eq_zero_or_oneₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))]
        []
        "with"
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [(Term.app `Or.inl [`n_odd])]
           "=>"
           (Term.match
            "match"
            []
            [(Term.matchDiscr [] (Term.app (Term.proj `Nat.even_iff "." (fieldIdx "2")) [`n_odd]))]
            []
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [(Term.anonymousCtor "⟨" [`m "," `twice_m] "⟩")]
               "=>"
               (Term.let
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `recurse
                  []
                  [(Term.typeSpec
                    ":"
                    («term_<_»
                     (Init.Logic.«term_+_» `m "+" (numLit "1"))
                     "<"
                     (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))))
                []
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (tacticCalc_
                      "calc"
                      [(calcStep
                        («term_=_»
                         (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "2")) "#")
                         "="
                         (Algebra.BigOperators.Basic.«term∏_in_,_»
                          "∏"
                          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                          " in "
                          (Term.app
                           `filter
                           [`prime
                            (Term.app
                             `range
                             [(Init.Logic.«term_+_»
                               (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                               "+"
                               (numLit "2"))])])
                          ", "
                          `i))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] ["←"] `twice_m)] "]"] [] [])
                             [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Algebra.BigOperators.Basic.«term∏_in_,_»
                          "∏"
                          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                          " in "
                          (Term.app
                           `filter
                           [`prime
                            (Init.Core.«term_∪_»
                             (Term.app
                              `Finset.ico
                              [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                               (Init.Logic.«term_+_»
                                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                "+"
                                (numLit "2"))])
                             " ∪ "
                             (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))]))])
                          ", "
                          `i))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [] `range_eq_Ico)
                                ","
                                (Tactic.rwRule [] `Finset.union_comm)
                                ","
                                (Tactic.rwRule [] `Finset.Ico_union_Ico_eq_Ico)]
                               "]")
                              [])
                             [])
                            (group (Tactic.exact "exact" `bot_le) [])
                            (group
                             (Tactic.simp
                              "simp"
                              []
                              ["only"]
                              ["[" [(Tactic.simpLemma [] [] `add_le_add_iff_right)] "]"]
                              [])
                             [])
                            (group (Tactic.linarith "linarith" [] [] []) [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Algebra.BigOperators.Basic.«term∏_in_,_»
                          "∏"
                          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                          " in "
                          (Init.Core.«term_∪_»
                           (Term.app
                            `filter
                            [`prime
                             (Term.app
                              `Finset.ico
                              [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                               (Init.Logic.«term_+_»
                                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                "+"
                                (numLit "2"))])])
                           " ∪ "
                           (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))
                          ", "
                          `i))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `filter_union)] "]") [])
                             [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Algebra.BigOperators.Basic.«term∏_in_,_»
                           "∏"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                           " in "
                           (Term.app
                            `filter
                            [`prime
                             (Term.app
                              `Finset.ico
                              [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                               (Init.Logic.«term_+_»
                                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                "+"
                                (numLit "2"))])])
                           ", "
                           `i)
                          "*"
                          (Algebra.BigOperators.Basic.«term∏_in_,_»
                           "∏"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                           " in "
                           (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])])
                           ", "
                           `i)))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.apply "apply" `Finset.prod_union) [])
                            (group
                             (Tactic.tacticHave_
                              "have"
                              (Term.haveDecl
                               (Term.haveIdDecl
                                [`disj []]
                                [(Term.typeSpec
                                  ":"
                                  (Term.app
                                   `Disjoint
                                   [(Term.app
                                     `Finset.ico
                                     [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                                      (Init.Logic.«term_+_»
                                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                       "+"
                                       (numLit "2"))])
                                    (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))]
                                ":="
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
                                       [(Tactic.simpLemma [] [] `Finset.disjoint_left)
                                        ","
                                        (Tactic.simpLemma [] [] `and_imp)
                                        ","
                                        (Tactic.simpLemma [] [] `Finset.mem_Ico)
                                        ","
                                        (Tactic.simpLemma [] [] `not_ltₓ)
                                        ","
                                        (Tactic.simpLemma [] [] `Finset.mem_range)]
                                       "]"]
                                      [])
                                     [])
                                    (group (Tactic.intro "intro" [(Term.hole "_") `pr (Term.hole "_")]) [])
                                    (group (Tactic.exact "exact" `pr) [])]))))))
                             [])
                            (group (Tactic.exact "exact" (Term.app `Finset.disjoint_filter_filter [`disj])) [])]))))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Algebra.BigOperators.Basic.«term∏_in_,_»
                           "∏"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                           " in "
                           (Term.app
                            `filter
                            [`prime
                             (Term.app
                              `Finset.ico
                              [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                               (Init.Logic.«term_+_»
                                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                "+"
                                (numLit "2"))])])
                           ", "
                           `i)
                          "*"
                          («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.exact
                              "exact"
                              (Term.app
                               `Nat.mul_le_mul_leftₓ
                               [(Term.hole "_")
                                (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `m "+" (numLit "1"))])]))
                             [])]))))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Term.app
                           `choose
                           [(Init.Logic.«term_+_»
                             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                             "+"
                             (numLit "1"))
                            (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                          "*"
                          («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.tacticHave_
                              "have"
                              (Term.haveDecl
                               (Term.haveIdDecl
                                [`s []]
                                [(Term.typeSpec
                                  ":"
                                  (Init.Core.«term_∣_»
                                   (Algebra.BigOperators.Basic.«term∏_in_,_»
                                    "∏"
                                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                                    " in "
                                    (Term.app
                                     `filter
                                     [`prime
                                      (Term.app
                                       `Finset.ico
                                       [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                                        (Init.Logic.«term_+_»
                                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                         "+"
                                         (numLit "2"))])])
                                    ", "
                                    `i)
                                   " ∣ "
                                   (Term.app
                                    `choose
                                    [(Init.Logic.«term_+_»
                                      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                      "+"
                                      (numLit "1"))
                                     (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                                ":="
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group
                                     (Tactic.refine'
                                      "refine'"
                                      (Term.app
                                       `prod_primes_dvd
                                       [(Term.app
                                         `choose
                                         [(Init.Logic.«term_+_»
                                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                           "+"
                                           (numLit "1"))
                                          (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                                        (Term.hole "_")
                                        (Term.hole "_")]))
                                     [])
                                    (group
                                     (Tactic.«tactic·._»
                                      "·"
                                      (Tactic.tacticSeq
                                       (Tactic.tacticSeq1Indented
                                        [(group (Tactic.intro "intro" [`a]) [])
                                         (group
                                          (Tactic.rwSeq
                                           "rw"
                                           []
                                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]")
                                           [])
                                          [])
                                         (group (Tactic.cc "cc") [])])))
                                     [])
                                    (group
                                     (Tactic.«tactic·._»
                                      "·"
                                      (Tactic.tacticSeq
                                       (Tactic.tacticSeq1Indented
                                        [(group (Tactic.intro "intro" [`a]) [])
                                         (group
                                          (Tactic.rwSeq
                                           "rw"
                                           []
                                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]")
                                           [])
                                          [])
                                         (group (Tactic.intro "intro" [`pr]) [])
                                         (group
                                          (Tactic.rcases
                                           "rcases"
                                           [(Tactic.casesTarget [] `pr)]
                                           ["with"
                                            (Tactic.rcasesPat.tuple
                                             "⟨"
                                             [(Tactic.rcasesPatLo
                                               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `size)])
                                               [])
                                              ","
                                              (Tactic.rcasesPatLo
                                               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `is_prime)])
                                               [])]
                                             "⟩")])
                                          [])
                                         (group
                                          (Tactic.simp
                                           "simp"
                                           []
                                           ["only"]
                                           ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                                           [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                                          [])
                                         (group
                                          (Tactic.rcases
                                           "rcases"
                                           [(Tactic.casesTarget [] `size)]
                                           ["with"
                                            (Tactic.rcasesPat.tuple
                                             "⟨"
                                             [(Tactic.rcasesPatLo
                                               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_big)])
                                               [])
                                              ","
                                              (Tactic.rcasesPatLo
                                               (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_small)])
                                               [])]
                                             "⟩")])
                                          [])
                                         (group
                                          (Tactic.exact
                                           "exact"
                                           (Term.app
                                            `dvd_choose_of_middling_prime
                                            [`a `is_prime `m `a_big (Term.app `nat.lt_succ_iff.mp [`a_small])]))
                                          [])])))
                                     [])]))))))
                             [])
                            (group
                             (Tactic.tacticHave_
                              "have"
                              (Term.haveDecl
                               (Term.haveIdDecl
                                [`r []]
                                [(Term.typeSpec
                                  ":"
                                  («term_≤_»
                                   (Algebra.BigOperators.Basic.«term∏_in_,_»
                                    "∏"
                                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                                    " in "
                                    (Term.app
                                     `filter
                                     [`prime
                                      (Term.app
                                       `Finset.ico
                                       [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                                        (Init.Logic.«term_+_»
                                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                         "+"
                                         (numLit "2"))])])
                                    ", "
                                    `i)
                                   "≤"
                                   (Term.app
                                    `choose
                                    [(Init.Logic.«term_+_»
                                      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                      "+"
                                      (numLit "1"))
                                     (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                                ":="
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group
                                     (Tactic.refine'
                                      "refine'"
                                      (Term.app
                                       (Term.explicit "@" `Nat.le_of_dvdₓ)
                                       [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
                                     [])
                                    (group
                                     (Tactic.exact
                                      "exact"
                                      (Term.app
                                       (Term.explicit "@" `choose_pos)
                                       [(Init.Logic.«term_+_»
                                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                         "+"
                                         (numLit "1"))
                                        (Init.Logic.«term_+_» `m "+" (numLit "1"))
                                        (Term.byTactic
                                         "by"
                                         (Tactic.tacticSeq
                                          (Tactic.tacticSeq1Indented
                                           [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
                                     [])]))))))
                             [])
                            (group
                             (Tactic.exact "exact" (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r]))
                             [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Term.app
                           `choose
                           [(Init.Logic.«term_+_»
                             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                             "+"
                             (numLit "1"))
                            `m])
                          "*"
                          («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))] "]")
                              [])
                             [])]))))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Finset.Data.Finset.Fold.«term_*_»
                          («term_^_» (numLit "4") "^" `m)
                          "*"
                          («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
                        ":="
                        (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])]))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         («term_^_»
                          (numLit "4")
                          "^"
                          (Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                           "+"
                           (numLit "1"))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.ringExp "ring_exp" []) [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `twice_m)] "]") [])
                             [])]))))])
                     [])])))))])))
          (Term.matchAlt
           "|"
           [(Term.app `Or.inr [`n_even])]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.obtain
                 "obtain"
                 [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `one_lt_n) "|" (Tactic.rcasesPat.one `n_le_one)])]
                 [":"
                  («term_∨_»
                   («term_<_» (numLit "1") "<" (Init.Logic.«term_+_» `n "+" (numLit "1")))
                   "∨"
                   («term_≤_» (Init.Logic.«term_+_» `n "+" (numLit "1")) "≤" (numLit "1")))]
                 [":=" [(Term.app `lt_or_leₓ [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])]])
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         []
                         (Term.app
                          `primorial_succ
                          [(Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
                           `n_even]))]
                       "]")
                      [])
                     [])
                    (group
                     (tacticCalc_
                      "calc"
                      [(calcStep
                        («term_≤_»
                         (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "1")) "#")
                         "≤"
                         («term_^_» (numLit "4") "^" `n.succ))
                        ":="
                        (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
                        ":="
                        (Term.app
                         `pow_le_pow
                         [(Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                          (Term.app `Nat.le_succₓ [(Term.hole "_")])]))])
                     [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`n_zero []]
                        [(Term.typeSpec ":" («term_=_» `n "=" (numLit "0")))]
                        ":="
                        (Term.app
                         (Term.proj `eq_bot_iff "." (fieldIdx "2"))
                         [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
                     [])
                    (group
                     (Lean.Tactic.normNum
                      "norm_num"
                      ["["
                       [(Tactic.simpLemma [] [] `n_zero)
                        ","
                        (Tactic.simpLemma [] [] `primorial)
                        ","
                        (Tactic.simpLemma [] [] `range_succ)
                        ","
                        (Tactic.simpLemma [] [] `prod_filter)
                        ","
                        (Tactic.simpLemma [] [] `not_prime_zero)
                        ","
                        (Tactic.simpLemma [] [] `prime_two)]
                       "]"]
                      [])
                     [])])))
                [])]))))])))])
    []))
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAltsWhereDecls', expected 'Lean.Parser.Term.matchAltsWhereDecls.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.match
   "match"
   []
   [(Term.matchDiscr [] (Term.app `Nat.mod_two_eq_zero_or_oneₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))]
   []
   "with"
   (Term.matchAlts
    [(Term.matchAlt
      "|"
      [(Term.app `Or.inl [`n_odd])]
      "=>"
      (Term.match
       "match"
       []
       [(Term.matchDiscr [] (Term.app (Term.proj `Nat.even_iff "." (fieldIdx "2")) [`n_odd]))]
       []
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [(Term.anonymousCtor "⟨" [`m "," `twice_m] "⟩")]
          "=>"
          (Term.let
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `recurse
             []
             [(Term.typeSpec
               ":"
               («term_<_» (Init.Logic.«term_+_» `m "+" (numLit "1")) "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))))
           []
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_=_»
                    (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "2")) "#")
                    "="
                    (Algebra.BigOperators.Basic.«term∏_in_,_»
                     "∏"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                     " in "
                     (Term.app
                      `filter
                      [`prime
                       (Term.app
                        `range
                        [(Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                          "+"
                          (numLit "2"))])])
                     ", "
                     `i))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] ["←"] `twice_m)] "]"] [] [])
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Algebra.BigOperators.Basic.«term∏_in_,_»
                     "∏"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                     " in "
                     (Term.app
                      `filter
                      [`prime
                       (Init.Core.«term_∪_»
                        (Term.app
                         `Finset.ico
                         [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                          (Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                           "+"
                           (numLit "2"))])
                        " ∪ "
                        (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))]))])
                     ", "
                     `i))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `range_eq_Ico)
                           ","
                           (Tactic.rwRule [] `Finset.union_comm)
                           ","
                           (Tactic.rwRule [] `Finset.Ico_union_Ico_eq_Ico)]
                          "]")
                         [])
                        [])
                       (group (Tactic.exact "exact" `bot_le) [])
                       (group
                        (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `add_le_add_iff_right)] "]"] [])
                        [])
                       (group (Tactic.linarith "linarith" [] [] []) [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Algebra.BigOperators.Basic.«term∏_in_,_»
                     "∏"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                     " in "
                     (Init.Core.«term_∪_»
                      (Term.app
                       `filter
                       [`prime
                        (Term.app
                         `Finset.ico
                         [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                          (Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                           "+"
                           (numLit "2"))])])
                      " ∪ "
                      (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))
                     ", "
                     `i))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `filter_union)] "]") [])
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Algebra.BigOperators.Basic.«term∏_in_,_»
                      "∏"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      (Term.app
                       `filter
                       [`prime
                        (Term.app
                         `Finset.ico
                         [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                          (Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                           "+"
                           (numLit "2"))])])
                      ", "
                      `i)
                     "*"
                     (Algebra.BigOperators.Basic.«term∏_in_,_»
                      "∏"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])])
                      ", "
                      `i)))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Tactic.apply "apply" `Finset.prod_union) [])
                       (group
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           [`disj []]
                           [(Term.typeSpec
                             ":"
                             (Term.app
                              `Disjoint
                              [(Term.app
                                `Finset.ico
                                [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                                 (Init.Logic.«term_+_»
                                  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                  "+"
                                  (numLit "2"))])
                               (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))]
                           ":="
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
                                  [(Tactic.simpLemma [] [] `Finset.disjoint_left)
                                   ","
                                   (Tactic.simpLemma [] [] `and_imp)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.mem_Ico)
                                   ","
                                   (Tactic.simpLemma [] [] `not_ltₓ)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.mem_range)]
                                  "]"]
                                 [])
                                [])
                               (group (Tactic.intro "intro" [(Term.hole "_") `pr (Term.hole "_")]) [])
                               (group (Tactic.exact "exact" `pr) [])]))))))
                        [])
                       (group (Tactic.exact "exact" (Term.app `Finset.disjoint_filter_filter [`disj])) [])]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Algebra.BigOperators.Basic.«term∏_in_,_»
                      "∏"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      (Term.app
                       `filter
                       [`prime
                        (Term.app
                         `Finset.ico
                         [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                          (Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                           "+"
                           (numLit "2"))])])
                      ", "
                      `i)
                     "*"
                     («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.exact
                         "exact"
                         (Term.app
                          `Nat.mul_le_mul_leftₓ
                          [(Term.hole "_")
                           (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `m "+" (numLit "1"))])]))
                        [])]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Term.app
                      `choose
                      [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                       (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                     "*"
                     («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           [`s []]
                           [(Term.typeSpec
                             ":"
                             (Init.Core.«term_∣_»
                              (Algebra.BigOperators.Basic.«term∏_in_,_»
                               "∏"
                               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                               " in "
                               (Term.app
                                `filter
                                [`prime
                                 (Term.app
                                  `Finset.ico
                                  [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                                   (Init.Logic.«term_+_»
                                    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                    "+"
                                    (numLit "2"))])])
                               ", "
                               `i)
                              " ∣ "
                              (Term.app
                               `choose
                               [(Init.Logic.«term_+_»
                                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                 "+"
                                 (numLit "1"))
                                (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group
                                (Tactic.refine'
                                 "refine'"
                                 (Term.app
                                  `prod_primes_dvd
                                  [(Term.app
                                    `choose
                                    [(Init.Logic.«term_+_»
                                      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                      "+"
                                      (numLit "1"))
                                     (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                                   (Term.hole "_")
                                   (Term.hole "_")]))
                                [])
                               (group
                                (Tactic.«tactic·._»
                                 "·"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group (Tactic.intro "intro" [`a]) [])
                                    (group
                                     (Tactic.rwSeq
                                      "rw"
                                      []
                                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]")
                                      [])
                                     [])
                                    (group (Tactic.cc "cc") [])])))
                                [])
                               (group
                                (Tactic.«tactic·._»
                                 "·"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group (Tactic.intro "intro" [`a]) [])
                                    (group
                                     (Tactic.rwSeq
                                      "rw"
                                      []
                                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]")
                                      [])
                                     [])
                                    (group (Tactic.intro "intro" [`pr]) [])
                                    (group
                                     (Tactic.rcases
                                      "rcases"
                                      [(Tactic.casesTarget [] `pr)]
                                      ["with"
                                       (Tactic.rcasesPat.tuple
                                        "⟨"
                                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `size)]) [])
                                         ","
                                         (Tactic.rcasesPatLo
                                          (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `is_prime)])
                                          [])]
                                        "⟩")])
                                     [])
                                    (group
                                     (Tactic.simp
                                      "simp"
                                      []
                                      ["only"]
                                      ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                                      [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                                     [])
                                    (group
                                     (Tactic.rcases
                                      "rcases"
                                      [(Tactic.casesTarget [] `size)]
                                      ["with"
                                       (Tactic.rcasesPat.tuple
                                        "⟨"
                                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_big)]) [])
                                         ","
                                         (Tactic.rcasesPatLo
                                          (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_small)])
                                          [])]
                                        "⟩")])
                                     [])
                                    (group
                                     (Tactic.exact
                                      "exact"
                                      (Term.app
                                       `dvd_choose_of_middling_prime
                                       [`a `is_prime `m `a_big (Term.app `nat.lt_succ_iff.mp [`a_small])]))
                                     [])])))
                                [])]))))))
                        [])
                       (group
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           [`r []]
                           [(Term.typeSpec
                             ":"
                             («term_≤_»
                              (Algebra.BigOperators.Basic.«term∏_in_,_»
                               "∏"
                               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                               " in "
                               (Term.app
                                `filter
                                [`prime
                                 (Term.app
                                  `Finset.ico
                                  [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                                   (Init.Logic.«term_+_»
                                    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                    "+"
                                    (numLit "2"))])])
                               ", "
                               `i)
                              "≤"
                              (Term.app
                               `choose
                               [(Init.Logic.«term_+_»
                                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                 "+"
                                 (numLit "1"))
                                (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group
                                (Tactic.refine'
                                 "refine'"
                                 (Term.app
                                  (Term.explicit "@" `Nat.le_of_dvdₓ)
                                  [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
                                [])
                               (group
                                (Tactic.exact
                                 "exact"
                                 (Term.app
                                  (Term.explicit "@" `choose_pos)
                                  [(Init.Logic.«term_+_»
                                    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                    "+"
                                    (numLit "1"))
                                   (Init.Logic.«term_+_» `m "+" (numLit "1"))
                                   (Term.byTactic
                                    "by"
                                    (Tactic.tacticSeq
                                     (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
                                [])]))))))
                        [])
                       (group (Tactic.exact "exact" (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r])) [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Term.app
                      `choose
                      [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                       `m])
                     "*"
                     («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))] "]")
                         [])
                        [])]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Finset.Data.Finset.Fold.«term_*_»
                     («term_^_» (numLit "4") "^" `m)
                     "*"
                     («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
                   ":="
                   (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])]))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    («term_^_»
                     (numLit "4")
                     "^"
                     (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.ringExp "ring_exp" []) [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `twice_m)] "]") [])
                        [])]))))])
                [])])))))])))
     (Term.matchAlt
      "|"
      [(Term.app `Or.inr [`n_even])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.obtain
            "obtain"
            [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `one_lt_n) "|" (Tactic.rcasesPat.one `n_le_one)])]
            [":"
             («term_∨_»
              («term_<_» (numLit "1") "<" (Init.Logic.«term_+_» `n "+" (numLit "1")))
              "∨"
              («term_≤_» (Init.Logic.«term_+_» `n "+" (numLit "1")) "≤" (numLit "1")))]
            [":=" [(Term.app `lt_or_leₓ [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])]])
           [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    []
                    (Term.app
                     `primorial_succ
                     [(Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
                      `n_even]))]
                  "]")
                 [])
                [])
               (group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_≤_»
                    (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "1")) "#")
                    "≤"
                    («term_^_» (numLit "4") "^" `n.succ))
                   ":="
                   (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
                   ":="
                   (Term.app
                    `pow_le_pow
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                     (Term.app `Nat.le_succₓ [(Term.hole "_")])]))])
                [])])))
           [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`n_zero []]
                   [(Term.typeSpec ":" («term_=_» `n "=" (numLit "0")))]
                   ":="
                   (Term.app
                    (Term.proj `eq_bot_iff "." (fieldIdx "2"))
                    [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
                [])
               (group
                (Lean.Tactic.normNum
                 "norm_num"
                 ["["
                  [(Tactic.simpLemma [] [] `n_zero)
                   ","
                   (Tactic.simpLemma [] [] `primorial)
                   ","
                   (Tactic.simpLemma [] [] `range_succ)
                   ","
                   (Tactic.simpLemma [] [] `prod_filter)
                   ","
                   (Tactic.simpLemma [] [] `not_prime_zero)
                   ","
                   (Tactic.simpLemma [] [] `prime_two)]
                  "]"]
                 [])
                [])])))
           [])]))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.match', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.match', expected 'Lean.Parser.Term.match.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `one_lt_n) "|" (Tactic.rcasesPat.one `n_le_one)])]
        [":"
         («term_∨_»
          («term_<_» (numLit "1") "<" (Init.Logic.«term_+_» `n "+" (numLit "1")))
          "∨"
          («term_≤_» (Init.Logic.«term_+_» `n "+" (numLit "1")) "≤" (numLit "1")))]
        [":=" [(Term.app `lt_or_leₓ [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `primorial_succ
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
                  `n_even]))]
              "]")
             [])
            [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_≤_»
                (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "1")) "#")
                "≤"
                («term_^_» (numLit "4") "^" `n.succ))
               ":="
               (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
              (calcStep
               («term_≤_» (Term.hole "_") "≤" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
               ":="
               (Term.app
                `pow_le_pow
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                 (Term.app `Nat.le_succₓ [(Term.hole "_")])]))])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`n_zero []]
               [(Term.typeSpec ":" («term_=_» `n "=" (numLit "0")))]
               ":="
               (Term.app
                (Term.proj `eq_bot_iff "." (fieldIdx "2"))
                [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
            [])
           (group
            (Lean.Tactic.normNum
             "norm_num"
             ["["
              [(Tactic.simpLemma [] [] `n_zero)
               ","
               (Tactic.simpLemma [] [] `primorial)
               ","
               (Tactic.simpLemma [] [] `range_succ)
               ","
               (Tactic.simpLemma [] [] `prod_filter)
               ","
               (Tactic.simpLemma [] [] `not_prime_zero)
               ","
               (Tactic.simpLemma [] [] `prime_two)]
              "]"]
             [])
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`n_zero []]
          [(Term.typeSpec ":" («term_=_» `n "=" (numLit "0")))]
          ":="
          (Term.app
           (Term.proj `eq_bot_iff "." (fieldIdx "2"))
           [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
       [])
      (group
       (Lean.Tactic.normNum
        "norm_num"
        ["["
         [(Tactic.simpLemma [] [] `n_zero)
          ","
          (Tactic.simpLemma [] [] `primorial)
          ","
          (Tactic.simpLemma [] [] `range_succ)
          ","
          (Tactic.simpLemma [] [] `prod_filter)
          ","
          (Tactic.simpLemma [] [] `not_prime_zero)
          ","
          (Tactic.simpLemma [] [] `prime_two)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Lean.Tactic.normNum
   "norm_num"
   ["["
    [(Tactic.simpLemma [] [] `n_zero)
     ","
     (Tactic.simpLemma [] [] `primorial)
     ","
     (Tactic.simpLemma [] [] `range_succ)
     ","
     (Tactic.simpLemma [] [] `prod_filter)
     ","
     (Tactic.simpLemma [] [] `not_prime_zero)
     ","
     (Tactic.simpLemma [] [] `prime_two)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Tactic.normNum', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `prime_two
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `not_prime_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `prod_filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `range_succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `primorial
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n_zero
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
     [`n_zero []]
     [(Term.typeSpec ":" («term_=_» `n "=" (numLit "0")))]
     ":="
     (Term.app
      (Term.proj `eq_bot_iff "." (fieldIdx "2"))
      [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `eq_bot_iff "." (fieldIdx "2"))
   [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n_le_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `succ_le_succ_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `succ_le_succ_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `eq_bot_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `eq_bot_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `n "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app
            `primorial_succ
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
             `n_even]))]
         "]")
        [])
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "1")) "#")
           "≤"
           («term_^_» (numLit "4") "^" `n.succ))
          ":="
          (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
         (calcStep
          («term_≤_» (Term.hole "_") "≤" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
          ":="
          (Term.app
           `pow_le_pow
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
            (Term.app `Nat.le_succₓ [(Term.hole "_")])]))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_≤_»
      (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "1")) "#")
      "≤"
      («term_^_» (numLit "4") "^" `n.succ))
     ":="
     (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))
    (calcStep
     («term_≤_» (Term.hole "_") "≤" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
     ":="
     (Term.app
      `pow_le_pow
      [(Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
       (Term.app `Nat.le_succₓ [(Term.hole "_")])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `pow_le_pow
   [(Term.byTactic
     "by"
     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
    (Term.app `Nat.le_succₓ [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.le_succₓ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.le_succₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Nat.le_succₓ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Lean.Tactic.normNum "norm_num" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Tactic.normNum', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pow_le_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.hole "_") "≤" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (numLit "4")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `primorial_le_4_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "1")) "#")
   "≤"
   («term_^_» (numLit "4") "^" `n.succ))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (numLit "4") "^" `n.succ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n.succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (numLit "4")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "1")) "#")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Primorial.«term_#»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       `primorial_succ
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
        `n_even]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `primorial_succ
   [(Term.byTactic
     "by"
     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
    `n_even])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n_even
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.linarith "linarith" [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.linarith', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `primorial_succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed [(Tactic.rcasesPat.one `one_lt_n) "|" (Tactic.rcasesPat.one `n_le_one)])]
   [":"
    («term_∨_»
     («term_<_» (numLit "1") "<" (Init.Logic.«term_+_» `n "+" (numLit "1")))
     "∨"
     («term_≤_» (Init.Logic.«term_+_» `n "+" (numLit "1")) "≤" (numLit "1")))]
   [":=" [(Term.app `lt_or_leₓ [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `lt_or_leₓ [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_or_leₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∨_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∨_»
   («term_<_» (numLit "1") "<" (Init.Logic.«term_+_» `n "+" (numLit "1")))
   "∨"
   («term_≤_» (Init.Logic.«term_+_» `n "+" (numLit "1")) "≤" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∨_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Init.Logic.«term_+_» `n "+" (numLit "1")) "≤" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
  («term_<_» (numLit "1") "<" (Init.Logic.«term_+_» `n "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 0, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_<_» (numLit "1") "<" (Init.Logic.«term_+_» `n "+" (numLit "1"))) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 30, (some 30, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatMed', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Or.inr [`n_even])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n_even
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Or.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.match
   "match"
   []
   [(Term.matchDiscr [] (Term.app (Term.proj `Nat.even_iff "." (fieldIdx "2")) [`n_odd]))]
   []
   "with"
   (Term.matchAlts
    [(Term.matchAlt
      "|"
      [(Term.anonymousCtor "⟨" [`m "," `twice_m] "⟩")]
      "=>"
      (Term.let
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `recurse
         []
         [(Term.typeSpec
           ":"
           («term_<_» (Init.Logic.«term_+_» `m "+" (numLit "1")) "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))))
       []
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_=_»
                (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "2")) "#")
                "="
                (Algebra.BigOperators.Basic.«term∏_in_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                 " in "
                 (Term.app
                  `filter
                  [`prime
                   (Term.app
                    `range
                    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
                 ", "
                 `i))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] ["←"] `twice_m)] "]"] [] []) [])]))))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Algebra.BigOperators.Basic.«term∏_in_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                 " in "
                 (Term.app
                  `filter
                  [`prime
                   (Init.Core.«term_∪_»
                    (Term.app
                     `Finset.ico
                     [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                      (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])
                    " ∪ "
                    (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))]))])
                 ", "
                 `i))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `range_eq_Ico)
                       ","
                       (Tactic.rwRule [] `Finset.union_comm)
                       ","
                       (Tactic.rwRule [] `Finset.Ico_union_Ico_eq_Ico)]
                      "]")
                     [])
                    [])
                   (group (Tactic.exact "exact" `bot_le) [])
                   (group
                    (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `add_le_add_iff_right)] "]"] [])
                    [])
                   (group (Tactic.linarith "linarith" [] [] []) [])]))))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Algebra.BigOperators.Basic.«term∏_in_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                 " in "
                 (Init.Core.«term_∪_»
                  (Term.app
                   `filter
                   [`prime
                    (Term.app
                     `Finset.ico
                     [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                      (Init.Logic.«term_+_»
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                       "+"
                       (numLit "2"))])])
                  " ∪ "
                  (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))
                 ", "
                 `i))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `filter_union)] "]") [])
                    [])]))))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Finset.Data.Finset.Fold.«term_*_»
                 (Algebra.BigOperators.Basic.«term∏_in_,_»
                  "∏"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                  " in "
                  (Term.app
                   `filter
                   [`prime
                    (Term.app
                     `Finset.ico
                     [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                      (Init.Logic.«term_+_»
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                       "+"
                       (numLit "2"))])])
                  ", "
                  `i)
                 "*"
                 (Algebra.BigOperators.Basic.«term∏_in_,_»
                  "∏"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                  " in "
                  (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])])
                  ", "
                  `i)))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.apply "apply" `Finset.prod_union) [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`disj []]
                       [(Term.typeSpec
                         ":"
                         (Term.app
                          `Disjoint
                          [(Term.app
                            `Finset.ico
                            [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                             (Init.Logic.«term_+_»
                              (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                              "+"
                              (numLit "2"))])
                           (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))]
                       ":="
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
                              [(Tactic.simpLemma [] [] `Finset.disjoint_left)
                               ","
                               (Tactic.simpLemma [] [] `and_imp)
                               ","
                               (Tactic.simpLemma [] [] `Finset.mem_Ico)
                               ","
                               (Tactic.simpLemma [] [] `not_ltₓ)
                               ","
                               (Tactic.simpLemma [] [] `Finset.mem_range)]
                              "]"]
                             [])
                            [])
                           (group (Tactic.intro "intro" [(Term.hole "_") `pr (Term.hole "_")]) [])
                           (group (Tactic.exact "exact" `pr) [])]))))))
                    [])
                   (group (Tactic.exact "exact" (Term.app `Finset.disjoint_filter_filter [`disj])) [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 (Algebra.BigOperators.Basic.«term∏_in_,_»
                  "∏"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                  " in "
                  (Term.app
                   `filter
                   [`prime
                    (Term.app
                     `Finset.ico
                     [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                      (Init.Logic.«term_+_»
                       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                       "+"
                       (numLit "2"))])])
                  ", "
                  `i)
                 "*"
                 («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `Nat.mul_le_mul_leftₓ
                      [(Term.hole "_") (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `m "+" (numLit "1"))])]))
                    [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 (Term.app
                  `choose
                  [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                   (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                 "*"
                 («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`s []]
                       [(Term.typeSpec
                         ":"
                         (Init.Core.«term_∣_»
                          (Algebra.BigOperators.Basic.«term∏_in_,_»
                           "∏"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                           " in "
                           (Term.app
                            `filter
                            [`prime
                             (Term.app
                              `Finset.ico
                              [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                               (Init.Logic.«term_+_»
                                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                "+"
                                (numLit "2"))])])
                           ", "
                           `i)
                          " ∣ "
                          (Term.app
                           `choose
                           [(Init.Logic.«term_+_»
                             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                             "+"
                             (numLit "1"))
                            (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.refine'
                             "refine'"
                             (Term.app
                              `prod_primes_dvd
                              [(Term.app
                                `choose
                                [(Init.Logic.«term_+_»
                                  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                  "+"
                                  (numLit "1"))
                                 (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                               (Term.hole "_")
                               (Term.hole "_")]))
                            [])
                           (group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group (Tactic.intro "intro" [`a]) [])
                                (group
                                 (Tactic.rwSeq
                                  "rw"
                                  []
                                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]")
                                  [])
                                 [])
                                (group (Tactic.cc "cc") [])])))
                            [])
                           (group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group (Tactic.intro "intro" [`a]) [])
                                (group
                                 (Tactic.rwSeq
                                  "rw"
                                  []
                                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]")
                                  [])
                                 [])
                                (group (Tactic.intro "intro" [`pr]) [])
                                (group
                                 (Tactic.rcases
                                  "rcases"
                                  [(Tactic.casesTarget [] `pr)]
                                  ["with"
                                   (Tactic.rcasesPat.tuple
                                    "⟨"
                                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `size)]) [])
                                     ","
                                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `is_prime)]) [])]
                                    "⟩")])
                                 [])
                                (group
                                 (Tactic.simp
                                  "simp"
                                  []
                                  ["only"]
                                  ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                                  [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                                 [])
                                (group
                                 (Tactic.rcases
                                  "rcases"
                                  [(Tactic.casesTarget [] `size)]
                                  ["with"
                                   (Tactic.rcasesPat.tuple
                                    "⟨"
                                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_big)]) [])
                                     ","
                                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_small)]) [])]
                                    "⟩")])
                                 [])
                                (group
                                 (Tactic.exact
                                  "exact"
                                  (Term.app
                                   `dvd_choose_of_middling_prime
                                   [`a `is_prime `m `a_big (Term.app `nat.lt_succ_iff.mp [`a_small])]))
                                 [])])))
                            [])]))))))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`r []]
                       [(Term.typeSpec
                         ":"
                         («term_≤_»
                          (Algebra.BigOperators.Basic.«term∏_in_,_»
                           "∏"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                           " in "
                           (Term.app
                            `filter
                            [`prime
                             (Term.app
                              `Finset.ico
                              [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                               (Init.Logic.«term_+_»
                                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                "+"
                                (numLit "2"))])])
                           ", "
                           `i)
                          "≤"
                          (Term.app
                           `choose
                           [(Init.Logic.«term_+_»
                             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                             "+"
                             (numLit "1"))
                            (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.refine'
                             "refine'"
                             (Term.app
                              (Term.explicit "@" `Nat.le_of_dvdₓ)
                              [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
                            [])
                           (group
                            (Tactic.exact
                             "exact"
                             (Term.app
                              (Term.explicit "@" `choose_pos)
                              [(Init.Logic.«term_+_»
                                (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                                "+"
                                (numLit "1"))
                               (Init.Logic.«term_+_» `m "+" (numLit "1"))
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
                            [])]))))))
                    [])
                   (group (Tactic.exact "exact" (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r])) [])]))))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Finset.Data.Finset.Fold.«term_*_»
                 (Term.app
                  `choose
                  [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1")) `m])
                 "*"
                 («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))] "]")
                     [])
                    [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 («term_^_» (numLit "4") "^" `m)
                 "*"
                 («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
               ":="
               (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_^_»
                 (numLit "4")
                 "^"
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.ringExp "ring_exp" []) [])]))))
              (calcStep
               («term_=_» (Term.hole "_") "=" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `twice_m)] "]") [])
                    [])]))))])
            [])])))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.match', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.match', expected 'Lean.Parser.Term.match.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `recurse
     []
     [(Term.typeSpec
       ":"
       («term_<_» (Init.Logic.«term_+_» `m "+" (numLit "1")) "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))))
   []
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "2")) "#")
            "="
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             (Term.app
              `filter
              [`prime
               (Term.app
                `range
                [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
             ", "
             `i))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] ["←"] `twice_m)] "]"] [] []) [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             (Term.app
              `filter
              [`prime
               (Init.Core.«term_∪_»
                (Term.app
                 `Finset.ico
                 [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])
                " ∪ "
                (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))]))])
             ", "
             `i))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `range_eq_Ico)
                   ","
                   (Tactic.rwRule [] `Finset.union_comm)
                   ","
                   (Tactic.rwRule [] `Finset.Ico_union_Ico_eq_Ico)]
                  "]")
                 [])
                [])
               (group (Tactic.exact "exact" `bot_le) [])
               (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `add_le_add_iff_right)] "]"] []) [])
               (group (Tactic.linarith "linarith" [] [] []) [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             (Init.Core.«term_∪_»
              (Term.app
               `filter
               [`prime
                (Term.app
                 `Finset.ico
                 [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
              " ∪ "
              (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))
             ", "
             `i))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `filter_union)] "]") []) [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Algebra.BigOperators.Basic.«term∏_in_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              " in "
              (Term.app
               `filter
               [`prime
                (Term.app
                 `Finset.ico
                 [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
              ", "
              `i)
             "*"
             (Algebra.BigOperators.Basic.«term∏_in_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              " in "
              (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])])
              ", "
              `i)))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.apply "apply" `Finset.prod_union) [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`disj []]
                   [(Term.typeSpec
                     ":"
                     (Term.app
                      `Disjoint
                      [(Term.app
                        `Finset.ico
                        [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                          "+"
                          (numLit "2"))])
                       (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))]
                   ":="
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
                          [(Tactic.simpLemma [] [] `Finset.disjoint_left)
                           ","
                           (Tactic.simpLemma [] [] `and_imp)
                           ","
                           (Tactic.simpLemma [] [] `Finset.mem_Ico)
                           ","
                           (Tactic.simpLemma [] [] `not_ltₓ)
                           ","
                           (Tactic.simpLemma [] [] `Finset.mem_range)]
                          "]"]
                         [])
                        [])
                       (group (Tactic.intro "intro" [(Term.hole "_") `pr (Term.hole "_")]) [])
                       (group (Tactic.exact "exact" `pr) [])]))))))
                [])
               (group (Tactic.exact "exact" (Term.app `Finset.disjoint_filter_filter [`disj])) [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Algebra.BigOperators.Basic.«term∏_in_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              " in "
              (Term.app
               `filter
               [`prime
                (Term.app
                 `Finset.ico
                 [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
              ", "
              `i)
             "*"
             («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `Nat.mul_le_mul_leftₓ
                  [(Term.hole "_") (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `m "+" (numLit "1"))])]))
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app
              `choose
              [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
               (Init.Logic.«term_+_» `m "+" (numLit "1"))])
             "*"
             («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`s []]
                   [(Term.typeSpec
                     ":"
                     (Init.Core.«term_∣_»
                      (Algebra.BigOperators.Basic.«term∏_in_,_»
                       "∏"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                       " in "
                       (Term.app
                        `filter
                        [`prime
                         (Term.app
                          `Finset.ico
                          [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                           (Init.Logic.«term_+_»
                            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                            "+"
                            (numLit "2"))])])
                       ", "
                       `i)
                      " ∣ "
                      (Term.app
                       `choose
                       [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                        (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.refine'
                         "refine'"
                         (Term.app
                          `prod_primes_dvd
                          [(Term.app
                            `choose
                            [(Init.Logic.«term_+_»
                              (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                              "+"
                              (numLit "1"))
                             (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                           (Term.hole "_")
                           (Term.hole "_")]))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.intro "intro" [`a]) [])
                            (group
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]")
                              [])
                             [])
                            (group (Tactic.cc "cc") [])])))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.intro "intro" [`a]) [])
                            (group
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]")
                              [])
                             [])
                            (group (Tactic.intro "intro" [`pr]) [])
                            (group
                             (Tactic.rcases
                              "rcases"
                              [(Tactic.casesTarget [] `pr)]
                              ["with"
                               (Tactic.rcasesPat.tuple
                                "⟨"
                                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `size)]) [])
                                 ","
                                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `is_prime)]) [])]
                                "⟩")])
                             [])
                            (group
                             (Tactic.simp
                              "simp"
                              []
                              ["only"]
                              ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                              [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                             [])
                            (group
                             (Tactic.rcases
                              "rcases"
                              [(Tactic.casesTarget [] `size)]
                              ["with"
                               (Tactic.rcasesPat.tuple
                                "⟨"
                                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_big)]) [])
                                 ","
                                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_small)]) [])]
                                "⟩")])
                             [])
                            (group
                             (Tactic.exact
                              "exact"
                              (Term.app
                               `dvd_choose_of_middling_prime
                               [`a `is_prime `m `a_big (Term.app `nat.lt_succ_iff.mp [`a_small])]))
                             [])])))
                        [])]))))))
                [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`r []]
                   [(Term.typeSpec
                     ":"
                     («term_≤_»
                      (Algebra.BigOperators.Basic.«term∏_in_,_»
                       "∏"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                       " in "
                       (Term.app
                        `filter
                        [`prime
                         (Term.app
                          `Finset.ico
                          [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                           (Init.Logic.«term_+_»
                            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                            "+"
                            (numLit "2"))])])
                       ", "
                       `i)
                      "≤"
                      (Term.app
                       `choose
                       [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                        (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.refine'
                         "refine'"
                         (Term.app
                          (Term.explicit "@" `Nat.le_of_dvdₓ)
                          [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
                        [])
                       (group
                        (Tactic.exact
                         "exact"
                         (Term.app
                          (Term.explicit "@" `choose_pos)
                          [(Init.Logic.«term_+_»
                            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                            "+"
                            (numLit "1"))
                           (Init.Logic.«term_+_» `m "+" (numLit "1"))
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
                        [])]))))))
                [])
               (group (Tactic.exact "exact" (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r])) [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app
              `choose
              [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1")) `m])
             "*"
             («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))] "]")
                 [])
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             («term_^_» (numLit "4") "^" `m)
             "*"
             («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
           ":="
           (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            («term_^_»
             (numLit "4")
             "^"
             (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.ringExp "ring_exp" []) [])]))))
          (calcStep
           («term_=_» (Term.hole "_") "=" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `twice_m)] "]") []) [])]))))])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "2")) "#")
           "="
           (Algebra.BigOperators.Basic.«term∏_in_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            " in "
            (Term.app
             `filter
             [`prime
              (Term.app
               `range
               [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
            ", "
            `i))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] ["←"] `twice_m)] "]"] [] []) [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∏_in_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            " in "
            (Term.app
             `filter
             [`prime
              (Init.Core.«term_∪_»
               (Term.app
                `Finset.ico
                [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])
               " ∪ "
               (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))]))])
            ", "
            `i))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `range_eq_Ico)
                  ","
                  (Tactic.rwRule [] `Finset.union_comm)
                  ","
                  (Tactic.rwRule [] `Finset.Ico_union_Ico_eq_Ico)]
                 "]")
                [])
               [])
              (group (Tactic.exact "exact" `bot_le) [])
              (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `add_le_add_iff_right)] "]"] []) [])
              (group (Tactic.linarith "linarith" [] [] []) [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∏_in_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            " in "
            (Init.Core.«term_∪_»
             (Term.app
              `filter
              [`prime
               (Term.app
                `Finset.ico
                [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
             " ∪ "
             (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))
            ", "
            `i))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `filter_union)] "]") []) [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             (Term.app
              `filter
              [`prime
               (Term.app
                `Finset.ico
                [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
             ", "
             `i)
            "*"
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])])
             ", "
             `i)))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.apply "apply" `Finset.prod_union) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`disj []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `Disjoint
                     [(Term.app
                       `Finset.ico
                       [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                         "+"
                         (numLit "2"))])
                      (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))]
                  ":="
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
                         [(Tactic.simpLemma [] [] `Finset.disjoint_left)
                          ","
                          (Tactic.simpLemma [] [] `and_imp)
                          ","
                          (Tactic.simpLemma [] [] `Finset.mem_Ico)
                          ","
                          (Tactic.simpLemma [] [] `not_ltₓ)
                          ","
                          (Tactic.simpLemma [] [] `Finset.mem_range)]
                         "]"]
                        [])
                       [])
                      (group (Tactic.intro "intro" [(Term.hole "_") `pr (Term.hole "_")]) [])
                      (group (Tactic.exact "exact" `pr) [])]))))))
               [])
              (group (Tactic.exact "exact" (Term.app `Finset.disjoint_filter_filter [`disj])) [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Algebra.BigOperators.Basic.«term∏_in_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             " in "
             (Term.app
              `filter
              [`prime
               (Term.app
                `Finset.ico
                [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                 (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
             ", "
             `i)
            "*"
            («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.exact
                "exact"
                (Term.app
                 `Nat.mul_le_mul_leftₓ
                 [(Term.hole "_") (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `m "+" (numLit "1"))])]))
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.app
             `choose
             [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
              (Init.Logic.«term_+_» `m "+" (numLit "1"))])
            "*"
            («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`s []]
                  [(Term.typeSpec
                    ":"
                    (Init.Core.«term_∣_»
                     (Algebra.BigOperators.Basic.«term∏_in_,_»
                      "∏"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      (Term.app
                       `filter
                       [`prime
                        (Term.app
                         `Finset.ico
                         [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                          (Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                           "+"
                           (numLit "2"))])])
                      ", "
                      `i)
                     " ∣ "
                     (Term.app
                      `choose
                      [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                       (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.refine'
                        "refine'"
                        (Term.app
                         `prod_primes_dvd
                         [(Term.app
                           `choose
                           [(Init.Logic.«term_+_»
                             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                             "+"
                             (numLit "1"))
                            (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                          (Term.hole "_")
                          (Term.hole "_")]))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.intro "intro" [`a]) [])
                           (group
                            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]") [])
                            [])
                           (group (Tactic.cc "cc") [])])))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.intro "intro" [`a]) [])
                           (group
                            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]") [])
                            [])
                           (group (Tactic.intro "intro" [`pr]) [])
                           (group
                            (Tactic.rcases
                             "rcases"
                             [(Tactic.casesTarget [] `pr)]
                             ["with"
                              (Tactic.rcasesPat.tuple
                               "⟨"
                               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `size)]) [])
                                ","
                                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `is_prime)]) [])]
                               "⟩")])
                            [])
                           (group
                            (Tactic.simp
                             "simp"
                             []
                             ["only"]
                             ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                             [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                            [])
                           (group
                            (Tactic.rcases
                             "rcases"
                             [(Tactic.casesTarget [] `size)]
                             ["with"
                              (Tactic.rcasesPat.tuple
                               "⟨"
                               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_big)]) [])
                                ","
                                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_small)]) [])]
                               "⟩")])
                            [])
                           (group
                            (Tactic.exact
                             "exact"
                             (Term.app
                              `dvd_choose_of_middling_prime
                              [`a `is_prime `m `a_big (Term.app `nat.lt_succ_iff.mp [`a_small])]))
                            [])])))
                       [])]))))))
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`r []]
                  [(Term.typeSpec
                    ":"
                    («term_≤_»
                     (Algebra.BigOperators.Basic.«term∏_in_,_»
                      "∏"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                      " in "
                      (Term.app
                       `filter
                       [`prime
                        (Term.app
                         `Finset.ico
                         [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                          (Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                           "+"
                           (numLit "2"))])])
                      ", "
                      `i)
                     "≤"
                     (Term.app
                      `choose
                      [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                       (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.refine'
                        "refine'"
                        (Term.app
                         (Term.explicit "@" `Nat.le_of_dvdₓ)
                         [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
                       [])
                      (group
                       (Tactic.exact
                        "exact"
                        (Term.app
                         (Term.explicit "@" `choose_pos)
                         [(Init.Logic.«term_+_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
                           "+"
                           (numLit "1"))
                          (Init.Logic.«term_+_» `m "+" (numLit "1"))
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
                       [])]))))))
               [])
              (group (Tactic.exact "exact" (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r])) [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.app
             `choose
             [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1")) `m])
            "*"
            («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))] "]")
                [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            («term_^_» (numLit "4") "^" `m)
            "*"
            («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
          ":="
          (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           («term_^_»
            (numLit "4")
            "^"
            (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.ringExp "ring_exp" []) [])]))))
         (calcStep
          («term_=_» (Term.hole "_") "=" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `twice_m)] "]") []) [])]))))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_»
      (NumberTheory.Primorial.«term_#» (Init.Logic.«term_+_» `n "+" (numLit "2")) "#")
      "="
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       (Term.app
        `filter
        [`prime
         (Term.app
          `range
          [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
       ", "
       `i))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.simpa "simpa" [] [] ["[" [(Tactic.simpLemma [] ["←"] `twice_m)] "]"] [] []) [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       (Term.app
        `filter
        [`prime
         (Init.Core.«term_∪_»
          (Term.app
           `Finset.ico
           [(Init.Logic.«term_+_» `m "+" (numLit "2"))
            (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])
          " ∪ "
          (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))]))])
       ", "
       `i))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `range_eq_Ico)
             ","
             (Tactic.rwRule [] `Finset.union_comm)
             ","
             (Tactic.rwRule [] `Finset.Ico_union_Ico_eq_Ico)]
            "]")
           [])
          [])
         (group (Tactic.exact "exact" `bot_le) [])
         (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `add_le_add_iff_right)] "]"] []) [])
         (group (Tactic.linarith "linarith" [] [] []) [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       (Init.Core.«term_∪_»
        (Term.app
         `filter
         [`prime
          (Term.app
           `Finset.ico
           [(Init.Logic.«term_+_» `m "+" (numLit "2"))
            (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
        " ∪ "
        (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))
       ", "
       `i))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `filter_union)] "]") []) [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Algebra.BigOperators.Basic.«term∏_in_,_»
        "∏"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        " in "
        (Term.app
         `filter
         [`prime
          (Term.app
           `Finset.ico
           [(Init.Logic.«term_+_» `m "+" (numLit "2"))
            (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
        ", "
        `i)
       "*"
       (Algebra.BigOperators.Basic.«term∏_in_,_»
        "∏"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        " in "
        (Term.app `filter [`prime (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])])
        ", "
        `i)))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.apply "apply" `Finset.prod_union) [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`disj []]
             [(Term.typeSpec
               ":"
               (Term.app
                `Disjoint
                [(Term.app
                  `Finset.ico
                  [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])
                 (Term.app `range [(Init.Logic.«term_+_» `m "+" (numLit "2"))])]))]
             ":="
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
                    [(Tactic.simpLemma [] [] `Finset.disjoint_left)
                     ","
                     (Tactic.simpLemma [] [] `and_imp)
                     ","
                     (Tactic.simpLemma [] [] `Finset.mem_Ico)
                     ","
                     (Tactic.simpLemma [] [] `not_ltₓ)
                     ","
                     (Tactic.simpLemma [] [] `Finset.mem_range)]
                    "]"]
                   [])
                  [])
                 (group (Tactic.intro "intro" [(Term.hole "_") `pr (Term.hole "_")]) [])
                 (group (Tactic.exact "exact" `pr) [])]))))))
          [])
         (group (Tactic.exact "exact" (Term.app `Finset.disjoint_filter_filter [`disj])) [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Algebra.BigOperators.Basic.«term∏_in_,_»
        "∏"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        " in "
        (Term.app
         `filter
         [`prime
          (Term.app
           `Finset.ico
           [(Init.Logic.«term_+_» `m "+" (numLit "2"))
            (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
        ", "
        `i)
       "*"
       («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.exact
           "exact"
           (Term.app
            `Nat.mul_le_mul_leftₓ
            [(Term.hole "_") (Term.app `primorial_le_4_pow [(Init.Logic.«term_+_» `m "+" (numLit "1"))])]))
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.app
        `choose
        [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
         (Init.Logic.«term_+_» `m "+" (numLit "1"))])
       "*"
       («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`s []]
             [(Term.typeSpec
               ":"
               (Init.Core.«term_∣_»
                (Algebra.BigOperators.Basic.«term∏_in_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                 " in "
                 (Term.app
                  `filter
                  [`prime
                   (Term.app
                    `Finset.ico
                    [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                     (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
                 ", "
                 `i)
                " ∣ "
                (Term.app
                 `choose
                 [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                  (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `prod_primes_dvd
                    [(Term.app
                      `choose
                      [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                       (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                     (Term.hole "_")
                     (Term.hole "_")]))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.intro "intro" [`a]) [])
                      (group
                       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]") [])
                       [])
                      (group (Tactic.cc "cc") [])])))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.intro "intro" [`a]) [])
                      (group
                       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]") [])
                       [])
                      (group (Tactic.intro "intro" [`pr]) [])
                      (group
                       (Tactic.rcases
                        "rcases"
                        [(Tactic.casesTarget [] `pr)]
                        ["with"
                         (Tactic.rcasesPat.tuple
                          "⟨"
                          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `size)]) [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `is_prime)]) [])]
                          "⟩")])
                       [])
                      (group
                       (Tactic.simp
                        "simp"
                        []
                        ["only"]
                        ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                        [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                       [])
                      (group
                       (Tactic.rcases
                        "rcases"
                        [(Tactic.casesTarget [] `size)]
                        ["with"
                         (Tactic.rcasesPat.tuple
                          "⟨"
                          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_big)]) [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_small)]) [])]
                          "⟩")])
                       [])
                      (group
                       (Tactic.exact
                        "exact"
                        (Term.app
                         `dvd_choose_of_middling_prime
                         [`a `is_prime `m `a_big (Term.app `nat.lt_succ_iff.mp [`a_small])]))
                       [])])))
                  [])]))))))
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`r []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                (Algebra.BigOperators.Basic.«term∏_in_,_»
                 "∏"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                 " in "
                 (Term.app
                  `filter
                  [`prime
                   (Term.app
                    `Finset.ico
                    [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                     (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
                 ", "
                 `i)
                "≤"
                (Term.app
                 `choose
                 [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                  (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.refine'
                   "refine'"
                   (Term.app (Term.explicit "@" `Nat.le_of_dvdₓ) [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
                  [])
                 (group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.explicit "@" `choose_pos)
                    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                     (Init.Logic.«term_+_» `m "+" (numLit "1"))
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
                  [])]))))))
          [])
         (group (Tactic.exact "exact" (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r])) [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.app
        `choose
        [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1")) `m])
       "*"
       («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))] "]") [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       («term_^_» (numLit "4") "^" `m)
       "*"
       («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
     ":="
     (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      («term_^_»
       (numLit "4")
       "^"
       (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))))
     ":="
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.ringExp "ring_exp" []) [])]))))
    (calcStep
     («term_=_» (Term.hole "_") "=" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `twice_m)] "]") []) [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `twice_m)] "]") []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `twice_m)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `twice_m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `n "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (numLit "4")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.ringExp "ring_exp" []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.ringExp "ring_exp" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ringExp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   («term_^_»
    (numLit "4")
    "^"
    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_»
   (numLit "4")
   "^"
   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (numLit "4")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `choose_middle_le_pow [`m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `choose_middle_le_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `choose_middle_le_pow [`m]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mul_le_mul_rightₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    («term_^_» (numLit "4") "^" `m)
    "*"
    («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_^_» (numLit "4") "^" `m)
   "*"
   («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `m "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (numLit "4")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_^_» (numLit "4") "^" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (numLit "4")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_^_» (numLit "4") "^" `m) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))] "]") [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `choose_symm_half [`m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `choose_symm_half
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app
     `choose
     [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1")) `m])
    "*"
    («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app
    `choose
    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1")) `m])
   "*"
   («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (numLit "4") "^" (Init.Logic.«term_+_» `m "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `m "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (numLit "4")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app
   `choose
   [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1")) `m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []] ")")
   "+"
   (numLit "1"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `choose
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`s []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∣_»
             (Algebra.BigOperators.Basic.«term∏_in_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              " in "
              (Term.app
               `filter
               [`prime
                (Term.app
                 `Finset.ico
                 [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
              ", "
              `i)
             " ∣ "
             (Term.app
              `choose
              [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
               (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `prod_primes_dvd
                 [(Term.app
                   `choose
                   [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                    (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                  (Term.hole "_")
                  (Term.hole "_")]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`a]) [])
                   (group
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]") [])
                    [])
                   (group (Tactic.cc "cc") [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`a]) [])
                   (group
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mem_filter)] "]") [])
                    [])
                   (group (Tactic.intro "intro" [`pr]) [])
                   (group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] `pr)]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `size)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `is_prime)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                     [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                    [])
                   (group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] `size)]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_big)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a_small)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `dvd_choose_of_middling_prime
                      [`a `is_prime `m `a_big (Term.app `nat.lt_succ_iff.mp [`a_small])]))
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`r []]
          [(Term.typeSpec
            ":"
            («term_≤_»
             (Algebra.BigOperators.Basic.«term∏_in_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              " in "
              (Term.app
               `filter
               [`prime
                (Term.app
                 `Finset.ico
                 [(Init.Logic.«term_+_» `m "+" (numLit "2"))
                  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
              ", "
              `i)
             "≤"
             (Term.app
              `choose
              [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
               (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app (Term.explicit "@" `Nat.le_of_dvdₓ) [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.explicit "@" `choose_pos)
                 [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
                  (Init.Logic.«term_+_» `m "+" (numLit "1"))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
               [])]))))))
       [])
      (group (Tactic.exact "exact" (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.mul_le_mul_rightₓ [(Term.hole "_") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nat.mul_le_mul_rightₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`r []]
     [(Term.typeSpec
       ":"
       («term_≤_»
        (Algebra.BigOperators.Basic.«term∏_in_,_»
         "∏"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         " in "
         (Term.app
          `filter
          [`prime
           (Term.app
            `Finset.ico
            [(Init.Logic.«term_+_» `m "+" (numLit "2"))
             (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
         ", "
         `i)
        "≤"
        (Term.app
         `choose
         [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
          (Init.Logic.«term_+_» `m "+" (numLit "1"))])))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.refine'
           "refine'"
           (Term.app (Term.explicit "@" `Nat.le_of_dvdₓ) [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            (Term.explicit "@" `choose_pos)
            [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
             (Init.Logic.«term_+_» `m "+" (numLit "1"))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app (Term.explicit "@" `Nat.le_of_dvdₓ) [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.explicit "@" `choose_pos)
         [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
          (Init.Logic.«term_+_» `m "+" (numLit "1"))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.explicit "@" `choose_pos)
    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
     (Init.Logic.«term_+_» `m "+" (numLit "1"))
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `choose_pos)
   [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
    (Init.Logic.«term_+_» `m "+" (numLit "1"))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.linarith "linarith" [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.linarith', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `m "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `m "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []] ")")
   "+"
   (numLit "1"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `choose_pos)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `choose_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app (Term.explicit "@" `Nat.le_of_dvdₓ) [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.explicit "@" `Nat.le_of_dvdₓ) [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `Nat.le_of_dvdₓ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nat.le_of_dvdₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    (Term.app
     `filter
     [`prime
      (Term.app
       `Finset.ico
       [(Init.Logic.«term_+_» `m "+" (numLit "2"))
        (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
    ", "
    `i)
   "≤"
   (Term.app
    `choose
    [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
     (Init.Logic.«term_+_» `m "+" (numLit "1"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `choose
   [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
    (Init.Logic.«term_+_» `m "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `m "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `m "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []] ")")
   "+"
   (numLit "1"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `choose
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   (Term.app
    `filter
    [`prime
     (Term.app
      `Finset.ico
      [(Init.Logic.«term_+_» `m "+" (numLit "2"))
       (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
   ", "
   `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `filter
   [`prime
    (Term.app
     `Finset.ico
     [(Init.Logic.«term_+_» `m "+" (numLit "2"))
      (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.ico
   [(Init.Logic.«term_+_» `m "+" (numLit "2"))
    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_»
   (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []] ")")
   "+"
   (numLit "2"))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `m "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `m "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.ico
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Finset.ico
   [(Term.paren "(" [(Init.Logic.«term_+_» `m "+" (numLit "2")) []] ")")
    (Term.paren
     "("
     [(Init.Logic.«term_+_»
       (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `m) []] ")")
       "+"
       (numLit "2"))
      []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `prime
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `filter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
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
  primorial_le_4_pow
  : ∀ n : ℕ , n # ≤ 4 ^ n
  | 0 => le_reflₓ _
    | 1 => le_of_inf_eq rfl
    |
      n + 2
      =>
      match
        Nat.mod_two_eq_zero_or_oneₓ n + 1
        with
        |
            Or.inl n_odd
            =>
            match
              Nat.even_iff . 2 n_odd
              with
              |
                ⟨ m , twice_m ⟩
                =>
                let
                  recurse : m + 1 < n + 2 := by linarith
                  by
                    calc
                      n + 2 # = ∏ i in filter prime range 2 * m + 2 , i := by simpa [ ← twice_m ]
                        _ = ∏ i in filter prime Finset.ico m + 2 2 * m + 2 ∪ range m + 2 , i
                          :=
                          by
                            rw [ range_eq_Ico , Finset.union_comm , Finset.Ico_union_Ico_eq_Ico ]
                              exact bot_le
                              simp only [ add_le_add_iff_right ]
                              linarith
                        _ = ∏ i in filter prime Finset.ico m + 2 2 * m + 2 ∪ filter prime range m + 2 , i
                          :=
                          by rw [ filter_union ]
                        _ = ∏ i in filter prime Finset.ico m + 2 2 * m + 2 , i * ∏ i in filter prime range m + 2 , i
                          :=
                          by
                            apply Finset.prod_union
                              have
                                disj
                                  : Disjoint Finset.ico m + 2 2 * m + 2 range m + 2
                                  :=
                                  by
                                    simp
                                        only
                                        [ Finset.disjoint_left , and_imp , Finset.mem_Ico , not_ltₓ , Finset.mem_range ]
                                      intro _ pr _
                                      exact pr
                              exact Finset.disjoint_filter_filter disj
                        _ ≤ ∏ i in filter prime Finset.ico m + 2 2 * m + 2 , i * 4 ^ m + 1
                          :=
                          by exact Nat.mul_le_mul_leftₓ _ primorial_le_4_pow m + 1
                        _ ≤ choose 2 * m + 1 m + 1 * 4 ^ m + 1
                          :=
                          by
                            have
                                s
                                  : ∏ i in filter prime Finset.ico m + 2 2 * m + 2 , i ∣ choose 2 * m + 1 m + 1
                                  :=
                                  by
                                    refine' prod_primes_dvd choose 2 * m + 1 m + 1 _ _
                                      · intro a rw [ Finset.mem_filter ] cc
                                      ·
                                        intro a
                                          rw [ Finset.mem_filter ]
                                          intro pr
                                          rcases pr with ⟨ size , is_prime ⟩
                                          simp only [ Finset.mem_Ico ] at size
                                          rcases size with ⟨ a_big , a_small ⟩
                                          exact
                                            dvd_choose_of_middling_prime a is_prime m a_big nat.lt_succ_iff.mp a_small
                              have
                                r
                                  : ∏ i in filter prime Finset.ico m + 2 2 * m + 2 , i ≤ choose 2 * m + 1 m + 1
                                  :=
                                  by refine' @ Nat.le_of_dvdₓ _ _ _ s exact @ choose_pos 2 * m + 1 m + 1 by linarith
                              exact Nat.mul_le_mul_rightₓ _ r
                        _ = choose 2 * m + 1 m * 4 ^ m + 1 := by rw [ choose_symm_half m ]
                        _ ≤ 4 ^ m * 4 ^ m + 1 := Nat.mul_le_mul_rightₓ _ choose_middle_le_pow m
                        _ = 4 ^ 2 * m + 1 := by ring_exp
                        _ = 4 ^ n + 2 := by rw [ ← twice_m ]
          |
            Or.inr n_even
            =>
            by
              obtain one_lt_n | n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := lt_or_leₓ 1 n + 1
                ·
                  rw [ primorial_succ by linarith n_even ]
                    calc
                      n + 1 # ≤ 4 ^ n.succ := primorial_le_4_pow n + 1
                        _ ≤ 4 ^ n + 2 := pow_le_pow by norm_num Nat.le_succₓ _
                ·
                  have n_zero : n = 0 := eq_bot_iff . 2 succ_le_succ_iff . 1 n_le_one
                    norm_num [ n_zero , primorial , range_succ , prod_filter , not_prime_zero , prime_two ]

