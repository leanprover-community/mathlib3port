import Mathbin.Topology.Instances.Real
import Mathbin.Order.Filter.Archimedean

/-!
# Convergence of subadditive sequences

A subadditive sequence `u : ℕ → ℝ` is a sequence satisfying `u (m + n) ≤ u m + u n` for all `m, n`.
We define this notion as `subadditive u`, and prove in `subadditive.tendsto_lim` that, if `u n / n`
is bounded below, then it converges to a limit (that we denote by `subadditive.lim` for
convenience). This result is known as Fekete's lemma in the literature.
-/


noncomputable section

open Set Filter

open_locale TopologicalSpace

/--  A real-valued sequence is subadditive if it satisfies the inequality `u (m + n) ≤ u m + u n`
for all `m, n`. -/
def Subadditive (u : ℕ → ℝ) : Prop :=
  ∀ m n, u (m+n) ≤ u m+u n

namespace Subadditive

variable {u : ℕ → ℝ} (h : Subadditive u)

include h

/--  The limit of a bounded-below subadditive sequence. The fact that the sequence indeed tends to
this limit is given in `subadditive.tendsto_lim` -/
@[nolint unused_arguments]
protected irreducible_def limₓ :=
  Inf ((fun n : ℕ => u n / n) '' Ici 1)

theorem lim_le_div (hbdd : BddBelow (range fun n => u n / n)) {n : ℕ} (hn : n ≠ 0) : h.lim ≤ u n / n := by
  rw [Subadditive.lim]
  apply cInf_le _ _
  ·
    rcases hbdd with ⟨c, hc⟩
    exact ⟨c, fun x hx => hc (image_subset_range _ _ hx)⟩
  ·
    apply mem_image_of_mem
    exact zero_lt_iff.2 hn

theorem apply_mul_add_le k n r : u ((k*n)+r) ≤ (k*u n)+u r := by
  induction' k with k IH
  ·
    simp only [Nat.cast_zero, zero_mul, zero_addₓ]
  calc u (((k+1)*n)+r) = u (n+(k*n)+r) := by
    congr 1
    ring _ ≤ u n+u ((k*n)+r) := h _ _ _ ≤ u n+(k*u n)+u r := add_le_add_left IH _ _ = ((k+1)*u n)+u r := by
    ring

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `eventually_div_lt_of_div_lt [])
  (Command.declSig
   [(Term.implicitBinder "{" [`L] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
    (Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
    (Term.explicitBinder "(" [`hn] [":" («term_≠_» `n "≠" (numLit "0"))] [] ")")
    (Term.explicitBinder "(" [`hL] [":" («term_<_» («term_/_» (Term.app `u [`n]) "/" `n) "<" `L)] [] ")")]
   (Term.typeSpec
    ":"
    (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
     "∀ᶠ"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
     " in "
     `at_top
     ", "
     («term_<_» («term_/_» (Term.app `u [`p]) "/" `p) "<" `L))))
  (Command.declValSimple
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
           [`I []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`i] [(Term.typeSpec ":" (termℕ "ℕ"))])]
              ","
              (Term.arrow
               («term_<_» (numLit "0") "<" `i)
               "→"
               («term_≠_»
                (Term.paren "(" [`i [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                "≠"
                (numLit "0")))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`i `hi]) [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `hi.ne')
                   ","
                   (Tactic.simpLemma [] [] `Ne.def)
                   ","
                   (Tactic.simpLemma [] [] `Nat.cast_eq_zero)
                   ","
                   (Tactic.simpLemma [] [] `not_false_iff)]
                  "]"]
                 [])
                [])]))))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `w)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `nw)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `wL)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `w)] []))
           ","
           («term_∧_» («term_<_» («term_/_» (Term.app `u [`n]) "/" `n) "<" `w) "∧" («term_<_» `w "<" `L)))]
         [":=" [(Term.app `exists_between [`hL])]])
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           ","
           (Term.forall
            "∀"
            []
            ","
            (Mathlib.ExtendedBinder.«term∀___,_»
             "∀"
             `i
             (Mathlib.ExtendedBinder.«binderTerm<_» "<" `n)
             ","
             (Term.forall
              "∀"
              []
              ","
              («term_≤_» («term_-_» (Term.app `u [`i]) "-" (Finset.Data.Finset.Fold.«term_*_» `i "*" `w)) "≤" `x)))))]
         [])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.obtain
              "obtain"
              [(Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                  "⟩")])]
              [":"
               (Term.app
                `BddAbove
                [(Init.Coe.«term↑_»
                  "↑"
                  (Term.app
                   `Finset.image
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`i] [])]
                      "=>"
                      («term_-_» (Term.app `u [`i]) "-" (Finset.Data.Finset.Fold.«term_*_» `i "*" `w))))
                    (Term.app `Finset.range [`n])]))])]
              [":=" [(Term.app `Finset.bdd_above [(Term.hole "_")])]])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`x "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))]
               "⟩"))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `UpperBounds)
                ","
                (Tactic.simpLemma [] [] `mem_image)
                ","
                (Tactic.simpLemma [] [] `and_imp)
                ","
                (Tactic.simpLemma [] [] `forall_exists_index)
                ","
                (Tactic.simpLemma [] [] `mem_set_of_eq)
                ","
                (Tactic.simpLemma [] [] `forall_apply_eq_imp_iff₂)
                ","
                (Tactic.simpLemma [] [] `Finset.mem_range)
                ","
                (Tactic.simpLemma [] [] `Finset.mem_coe)
                ","
                (Tactic.simpLemma [] [] `Finset.coe_image)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
             [])
            (group (Tactic.exact "exact" (Term.app `hx [(Term.hole "_") `hi])) [])])))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`A []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
              ","
              («term_≤_»
               (Term.app `u [`p])
               "≤"
               (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `p "*" `w) "+" `x))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`p]) [])
               (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `s [] ":=" («term_/_» `p "/" `n)))) [])
               (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `r [] ":=" («term_%_» `p "%" `n)))) [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hp []]
                   [(Term.typeSpec
                     ":"
                     («term_=_» `p "=" (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `s "*" `n) "+" `r)))]
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
                          [(Tactic.rwRule [] `mul_commₓ) "," (Tactic.rwRule [] `Nat.div_add_mod)]
                          "]")
                         [])
                        [])]))))))
                [])
               (group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_=_»
                    (Term.app `u [`p])
                    "="
                    (Term.app `u [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `s "*" `n) "+" `r)]))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp)] "]") []) [])]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Init.Logic.«term_+_»
                     (Finset.Data.Finset.Fold.«term_*_» `s "*" (Term.app `u [`n]))
                     "+"
                     (Term.app `u [`r])))
                   ":="
                   (Term.app `h.apply_mul_add_le [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Init.Logic.«term_+_»
                     (Finset.Data.Finset.Fold.«term_*_»
                      (Finset.Data.Finset.Fold.«term_*_» `s "*" `n)
                      "*"
                      («term_/_» (Term.app `u [`n]) "/" `n))
                     "+"
                     (Term.app `u [`r])))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.fieldSimp
                         "field_simp"
                         []
                         []
                         ["[" [(Tactic.simpLemma [] [] (Term.app `I [(Term.hole "_") `hn.bot_lt]))] "]"]
                         []
                         [])
                        [])
                       (group (Tactic.Ring.tacticRing "ring") [])]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Init.Logic.«term_+_»
                     (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» `s "*" `n) "*" `w)
                     "+"
                     (Term.app `u [`r])))
                   ":="
                   (Term.app
                    `add_le_add_right
                    [(Term.app
                      `mul_le_mul_of_nonneg_left
                      [`nw.le
                       (Term.app
                        `mul_nonneg
                        [(Term.app `Nat.cast_nonneg [(Term.hole "_")]) (Term.app `Nat.cast_nonneg [(Term.hole "_")])])])
                     (Term.hole "_")]))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Init.Logic.«term_+_»
                     (Finset.Data.Finset.Fold.«term_*_»
                      (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `s "*" `n) "+" `r)
                      "*"
                      `w)
                     "+"
                     («term_-_» (Term.app `u [`r]) "-" (Finset.Data.Finset.Fold.«term_*_» `r "*" `w))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Init.Logic.«term_+_»
                     (Finset.Data.Finset.Fold.«term_*_» `p "*" `w)
                     "+"
                     («term_-_» (Term.app `u [`r]) "-" (Finset.Data.Finset.Fold.«term_*_» `r "*" `w))))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp)] "]") []) [])
                       (group
                        (Tactic.simp
                         "simp"
                         []
                         ["only"]
                         ["[" [(Tactic.simpLemma [] [] `Nat.cast_add) "," (Tactic.simpLemma [] [] `Nat.cast_mul)] "]"]
                         [])
                        [])]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `p "*" `w) "+" `x))
                   ":="
                   (Term.app
                    `add_le_add_left
                    [(Term.app `hx [(Term.hole "_") (Term.app `Nat.mod_ltₓ [(Term.hole "_") `hn.bot_lt])])
                     (Term.hole "_")]))])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`B []]
           [(Term.typeSpec
             ":"
             (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
              "∀ᶠ"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
              " in "
              `at_top
              ", "
              («term_≤_»
               («term_/_» (Term.app `u [`p]) "/" `p)
               "≤"
               (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p)))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  (Term.proj `eventually_at_top "." (fieldIdx "2"))
                  [(Term.anonymousCtor
                    "⟨"
                    [(numLit "1")
                     ","
                     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`p `hp] [])] "=>" (Term.hole "_")))]
                    "⟩")]))
                [])
               (group
                (Tactic.simp'
                 "simp'"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] (Term.app `I [`p `hp]))
                   ","
                   (Tactic.simpLemma [] [] `Ne.def)
                   ","
                   (Tactic.simpLemma [] [] `not_false_iff)]
                  "]"]
                 ["with" [`field_simps]]
                 [])
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.app `div_le_div_of_le_of_nonneg [(Term.hole "_") (Term.app `Nat.cast_nonneg [(Term.hole "_")])]))
                [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_commₓ)] "]") []) [])
               (group (Tactic.exact "exact" (Term.app `A [(Term.hole "_")])) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`C []]
           [(Term.typeSpec
             ":"
             (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
              "∀ᶠ"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" (termℕ "ℕ")]))
              " in "
              `at_top
              ", "
              («term_<_» (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p)) "<" `L)))]
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
                   []
                   [(Term.typeSpec
                     ":"
                     (Term.app
                      `tendsto
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                         "=>"
                         (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))))
                       `at_top
                       (Term.app (Topology.Basic.term𝓝 "𝓝") [(Init.Logic.«term_+_» `w "+" (numLit "0"))])]))]
                   ":="
                   (Term.app
                    `tendsto_const_nhds.add
                    [(Term.app `tendsto_const_nhds.div_at_top [`tendsto_coe_nat_at_top_at_top])]))))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this]) "." (fieldIdx "2"))
                  [(Term.hole "_") `wL]))
                [])]))))))
        [])
       (group (Tactic.filterUpwards "filter_upwards" "[" [`B "," `C] "]" []) [])
       (group (Tactic.intro "intro" [`p `hp `h'p]) [])
       (group (Tactic.exact "exact" (Term.app `hp.trans_lt [`h'p])) [])])))
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`I []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`i] [(Term.typeSpec ":" (termℕ "ℕ"))])]
             ","
             (Term.arrow
              («term_<_» (numLit "0") "<" `i)
              "→"
              («term_≠_»
               (Term.paren "(" [`i [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
               "≠"
               (numLit "0")))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`i `hi]) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `hi.ne')
                  ","
                  (Tactic.simpLemma [] [] `Ne.def)
                  ","
                  (Tactic.simpLemma [] [] `Nat.cast_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] `not_false_iff)]
                 "]"]
                [])
               [])]))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `w)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `nw)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `wL)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `w)] []))
          ","
          («term_∧_» («term_<_» («term_/_» (Term.app `u [`n]) "/" `n) "<" `w) "∧" («term_<_» `w "<" `L)))]
        [":=" [(Term.app `exists_between [`hL])]])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          ","
          (Term.forall
           "∀"
           []
           ","
           (Mathlib.ExtendedBinder.«term∀___,_»
            "∀"
            `i
            (Mathlib.ExtendedBinder.«binderTerm<_» "<" `n)
            ","
            (Term.forall
             "∀"
             []
             ","
             («term_≤_» («term_-_» (Term.app `u [`i]) "-" (Finset.Data.Finset.Fold.«term_*_» `i "*" `w)) "≤" `x)))))]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                 "⟩")])]
             [":"
              (Term.app
               `BddAbove
               [(Init.Coe.«term↑_»
                 "↑"
                 (Term.app
                  `Finset.image
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`i] [])]
                     "=>"
                     («term_-_» (Term.app `u [`i]) "-" (Finset.Data.Finset.Fold.«term_*_» `i "*" `w))))
                   (Term.app `Finset.range [`n])]))])]
             [":=" [(Term.app `Finset.bdd_above [(Term.hole "_")])]])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`x "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))]
              "⟩"))
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `UpperBounds)
               ","
               (Tactic.simpLemma [] [] `mem_image)
               ","
               (Tactic.simpLemma [] [] `and_imp)
               ","
               (Tactic.simpLemma [] [] `forall_exists_index)
               ","
               (Tactic.simpLemma [] [] `mem_set_of_eq)
               ","
               (Tactic.simpLemma [] [] `forall_apply_eq_imp_iff₂)
               ","
               (Tactic.simpLemma [] [] `Finset.mem_range)
               ","
               (Tactic.simpLemma [] [] `Finset.mem_coe)
               ","
               (Tactic.simpLemma [] [] `Finset.coe_image)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
            [])
           (group (Tactic.exact "exact" (Term.app `hx [(Term.hole "_") `hi])) [])])))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`A []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
             ","
             («term_≤_»
              (Term.app `u [`p])
              "≤"
              (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `p "*" `w) "+" `x))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`p]) [])
              (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `s [] ":=" («term_/_» `p "/" `n)))) [])
              (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `r [] ":=" («term_%_» `p "%" `n)))) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hp []]
                  [(Term.typeSpec
                    ":"
                    («term_=_» `p "=" (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `s "*" `n) "+" `r)))]
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
                         [(Tactic.rwRule [] `mul_commₓ) "," (Tactic.rwRule [] `Nat.div_add_mod)]
                         "]")
                        [])
                       [])]))))))
               [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_=_»
                   (Term.app `u [`p])
                   "="
                   (Term.app `u [(Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `s "*" `n) "+" `r)]))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp)] "]") []) [])]))))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_» `s "*" (Term.app `u [`n]))
                    "+"
                    (Term.app `u [`r])))
                  ":="
                  (Term.app `h.apply_mul_add_le [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Finset.Data.Finset.Fold.«term_*_» `s "*" `n)
                     "*"
                     («term_/_» (Term.app `u [`n]) "/" `n))
                    "+"
                    (Term.app `u [`r])))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.fieldSimp
                        "field_simp"
                        []
                        []
                        ["[" [(Tactic.simpLemma [] [] (Term.app `I [(Term.hole "_") `hn.bot_lt]))] "]"]
                        []
                        [])
                       [])
                      (group (Tactic.Ring.tacticRing "ring") [])]))))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» `s "*" `n) "*" `w)
                    "+"
                    (Term.app `u [`r])))
                  ":="
                  (Term.app
                   `add_le_add_right
                   [(Term.app
                     `mul_le_mul_of_nonneg_left
                     [`nw.le
                      (Term.app
                       `mul_nonneg
                       [(Term.app `Nat.cast_nonneg [(Term.hole "_")]) (Term.app `Nat.cast_nonneg [(Term.hole "_")])])])
                    (Term.hole "_")]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `s "*" `n) "+" `r)
                     "*"
                     `w)
                    "+"
                    («term_-_» (Term.app `u [`r]) "-" (Finset.Data.Finset.Fold.«term_*_» `r "*" `w))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Init.Logic.«term_+_»
                    (Finset.Data.Finset.Fold.«term_*_» `p "*" `w)
                    "+"
                    («term_-_» (Term.app `u [`r]) "-" (Finset.Data.Finset.Fold.«term_*_» `r "*" `w))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hp)] "]") []) [])
                      (group
                       (Tactic.simp
                        "simp"
                        []
                        ["only"]
                        ["[" [(Tactic.simpLemma [] [] `Nat.cast_add) "," (Tactic.simpLemma [] [] `Nat.cast_mul)] "]"]
                        [])
                       [])]))))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Init.Logic.«term_+_» (Finset.Data.Finset.Fold.«term_*_» `p "*" `w) "+" `x))
                  ":="
                  (Term.app
                   `add_le_add_left
                   [(Term.app `hx [(Term.hole "_") (Term.app `Nat.mod_ltₓ [(Term.hole "_") `hn.bot_lt])])
                    (Term.hole "_")]))])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`B []]
          [(Term.typeSpec
            ":"
            (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
             "∀ᶠ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] []))
             " in "
             `at_top
             ", "
             («term_≤_»
              («term_/_» (Term.app `u [`p]) "/" `p)
              "≤"
              (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p)))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj `eventually_at_top "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(numLit "1")
                    ","
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`p `hp] [])] "=>" (Term.hole "_")))]
                   "⟩")]))
               [])
              (group
               (Tactic.simp'
                "simp'"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] (Term.app `I [`p `hp]))
                  ","
                  (Tactic.simpLemma [] [] `Ne.def)
                  ","
                  (Tactic.simpLemma [] [] `not_false_iff)]
                 "]"]
                ["with" [`field_simps]]
                [])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app `div_le_div_of_le_of_nonneg [(Term.hole "_") (Term.app `Nat.cast_nonneg [(Term.hole "_")])]))
               [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_commₓ)] "]") []) [])
              (group (Tactic.exact "exact" (Term.app `A [(Term.hole "_")])) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`C []]
          [(Term.typeSpec
            ":"
            (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
             "∀ᶠ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" (termℕ "ℕ")]))
             " in "
             `at_top
             ", "
             («term_<_» (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p)) "<" `L)))]
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
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `tendsto
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                        "=>"
                        (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))))
                      `at_top
                      (Term.app (Topology.Basic.term𝓝 "𝓝") [(Init.Logic.«term_+_» `w "+" (numLit "0"))])]))]
                  ":="
                  (Term.app
                   `tendsto_const_nhds.add
                   [(Term.app `tendsto_const_nhds.div_at_top [`tendsto_coe_nat_at_top_at_top])]))))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this]) "." (fieldIdx "2"))
                 [(Term.hole "_") `wL]))
               [])]))))))
       [])
      (group (Tactic.filterUpwards "filter_upwards" "[" [`B "," `C] "]" []) [])
      (group (Tactic.intro "intro" [`p `hp `h'p]) [])
      (group (Tactic.exact "exact" (Term.app `hp.trans_lt [`h'p])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `hp.trans_lt [`h'p]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hp.trans_lt [`h'p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h'p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hp.trans_lt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`p `hp `h'p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h'p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.filterUpwards "filter_upwards" "[" [`B "," `C] "]" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.filterUpwards', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `B
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
     [`C []]
     [(Term.typeSpec
       ":"
       (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
        "∀ᶠ"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" (termℕ "ℕ")]))
        " in "
        `at_top
        ", "
        («term_<_» (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p)) "<" `L)))]
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
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                   "=>"
                   (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))))
                 `at_top
                 (Term.app (Topology.Basic.term𝓝 "𝓝") [(Init.Logic.«term_+_» `w "+" (numLit "0"))])]))]
             ":="
             (Term.app
              `tendsto_const_nhds.add
              [(Term.app `tendsto_const_nhds.div_at_top [`tendsto_coe_nat_at_top_at_top])]))))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this]) "." (fieldIdx "2"))
            [(Term.hole "_") `wL]))
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.app
             `tendsto
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                "=>"
                (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))))
              `at_top
              (Term.app (Topology.Basic.term𝓝 "𝓝") [(Init.Logic.«term_+_» `w "+" (numLit "0"))])]))]
          ":="
          (Term.app
           `tendsto_const_nhds.add
           [(Term.app `tendsto_const_nhds.div_at_top [`tendsto_coe_nat_at_top_at_top])]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this]) "." (fieldIdx "2"))
         [(Term.hole "_") `wL]))
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
    (Term.proj (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this]) "." (fieldIdx "2"))
    [(Term.hole "_") `wL]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this]) "." (fieldIdx "2"))
   [(Term.hole "_") `wL])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `wL
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
  (Term.proj (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `tendsto_order "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `tendsto_order
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_zeroₓ
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
     []
     [(Term.typeSpec
       ":"
       (Term.app
        `tendsto
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
           "=>"
           (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))))
         `at_top
         (Term.app (Topology.Basic.term𝓝 "𝓝") [(Init.Logic.«term_+_» `w "+" (numLit "0"))])]))]
     ":="
     (Term.app `tendsto_const_nhds.add [(Term.app `tendsto_const_nhds.div_at_top [`tendsto_coe_nat_at_top_at_top])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `tendsto_const_nhds.add [(Term.app `tendsto_const_nhds.div_at_top [`tendsto_coe_nat_at_top_at_top])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `tendsto_const_nhds.div_at_top [`tendsto_coe_nat_at_top_at_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tendsto_coe_nat_at_top_at_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tendsto_const_nhds.div_at_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `tendsto_const_nhds.div_at_top [`tendsto_coe_nat_at_top_at_top]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tendsto_const_nhds.add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `tendsto
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
      "=>"
      (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))))
    `at_top
    (Term.app (Topology.Basic.term𝓝 "𝓝") [(Init.Logic.«term_+_» `w "+" (numLit "0"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [(Init.Logic.«term_+_» `w "+" (numLit "0"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `w "+" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `w "+" (numLit "0")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Topology.Basic.term𝓝 "𝓝") [(Term.paren "(" [(Init.Logic.«term_+_» `w "+" (numLit "0")) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `at_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
    "=>"
    (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» `x "/" `p)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`p] [(Term.typeSpec ":" (termℕ "ℕ"))])]
    "=>"
    (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tendsto
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" (termℕ "ℕ")]))
   " in "
   `at_top
   ", "
   («term_<_» (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p)) "<" `L))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p)) "<" `L)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `L
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» `x "/" `p)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_» `w "+" («term_/_» `x "/" `p)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `at_top
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
  eventually_div_lt_of_div_lt
  { L : ℝ } { n : ℕ } ( hn : n ≠ 0 ) ( hL : u n / n < L ) : ∀ᶠ p in at_top , u p / p < L
  :=
    by
      have
          I
            : ∀ i : ℕ , 0 < i → ( i : ℝ ) ≠ 0
            :=
            by intro i hi simp only [ hi.ne' , Ne.def , Nat.cast_eq_zero , not_false_iff ]
        obtain ⟨ w , nw , wL ⟩ : ∃ w , u n / n < w ∧ w < L := exists_between hL
        obtain ⟨ x , hx ⟩ : ∃ x , ∀ , ∀ i < n , ∀ , u i - i * w ≤ x
        ·
          obtain ⟨ x , hx ⟩ : BddAbove ↑ Finset.image fun i => u i - i * w Finset.range n := Finset.bdd_above _
            refine' ⟨ x , fun i hi => _ ⟩
            simp
              only
              [
                UpperBounds
                  ,
                  mem_image
                  ,
                  and_imp
                  ,
                  forall_exists_index
                  ,
                  mem_set_of_eq
                  ,
                  forall_apply_eq_imp_iff₂
                  ,
                  Finset.mem_range
                  ,
                  Finset.mem_coe
                  ,
                  Finset.coe_image
                ]
              at hx
            exact hx _ hi
        have
          A
            : ∀ p : ℕ , u p ≤ p * w + x
            :=
            by
              intro p
                let s := p / n
                let r := p % n
                have hp : p = s * n + r := by rw [ mul_commₓ , Nat.div_add_mod ]
                calc
                  u p = u s * n + r := by rw [ hp ]
                    _ ≤ s * u n + u r := h.apply_mul_add_le _ _ _
                    _ = s * n * u n / n + u r := by field_simp [ I _ hn.bot_lt ] ring
                    _ ≤ s * n * w + u r
                      :=
                      add_le_add_right mul_le_mul_of_nonneg_left nw.le mul_nonneg Nat.cast_nonneg _ Nat.cast_nonneg _ _
                    _ = s * n + r * w + u r - r * w := by ring
                    _ = p * w + u r - r * w := by rw [ hp ] simp only [ Nat.cast_add , Nat.cast_mul ]
                    _ ≤ p * w + x := add_le_add_left hx _ Nat.mod_ltₓ _ hn.bot_lt _
        have
          B
            : ∀ᶠ p in at_top , u p / p ≤ w + x / p
            :=
            by
              refine' eventually_at_top . 2 ⟨ 1 , fun p hp => _ ⟩
                simp' only [ I p hp , Ne.def , not_false_iff ] with field_simps
                refine' div_le_div_of_le_of_nonneg _ Nat.cast_nonneg _
                rw [ mul_commₓ ]
                exact A _
        have
          C
            : ∀ᶠ p : ℕ in at_top , w + x / p < L
            :=
            by
              have
                  : tendsto fun p : ℕ => w + x / p at_top 𝓝 w + 0
                    :=
                    tendsto_const_nhds.add tendsto_const_nhds.div_at_top tendsto_coe_nat_at_top_at_top
                rw [ add_zeroₓ ] at this
                exact tendsto_order . 1 this . 2 _ wL
        filter_upwards [ B , C ]
        intro p hp h'p
        exact hp.trans_lt h'p

/--  Fekete's lemma: a subadditive sequence which is bounded below converges. -/
theorem tendsto_lim (hbdd : BddBelow (range fun n => u n / n)) : tendsto (fun n => u n / n) at_top (𝓝 h.lim) := by
  refine' tendsto_order.2 ⟨fun l hl => _, fun L hL => _⟩
  ·
    refine' eventually_at_top.2 ⟨1, fun n hn => hl.trans_le (h.lim_le_div hbdd (zero_lt_one.trans_le hn).ne')⟩
  ·
    obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ u n / n < L
    ·
      rw [Subadditive.lim] at hL
      rcases exists_lt_of_cInf_lt
          (by
            simp )
          hL with
        ⟨x, hx, xL⟩
      rcases(mem_image _ _ _).1 hx with ⟨n, hn, rfl⟩
      exact ⟨n, zero_lt_one.trans_le hn, xL⟩
    exact h.eventually_div_lt_of_div_lt npos.ne' hn

end Subadditive

