import Mathbin.Topology.MetricSpace.EmetricSpace
import Mathbin.Topology.Paracompact
import Mathbin.SetTheory.Ordinal

/-!
# (Extended) metric spaces are paracompact

In this file we provide two instances:

* `emetric.paracompact_space`: a `pseudo_emetric_space` is paracompact; formalization is based
  on [MR0236876];
* `emetric.normal_of_metric`: an `emetric_space` is a normal topological space.

## Tags

metric space, paracompact space, normal space
-/


variable {α : Type _}

open_locale Ennreal TopologicalSpace

open Set

namespace Emetric

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (m «expr ≤ » «expr + »(n, k))
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (i «expr ∈ » {i : ι | «expr ∩ »(D m i, B).nonempty})
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " A `pseudo_emetric_space` is always a paracompact space. Formalization is based\non [MR0236876]. -/")]
  []
  []
  []
  []
  [])
 (Command.instance
  (Term.attrKind [])
  "instance"
  [(Command.namedPrio "(" "priority" ":=" (numLit "100") ")")]
  []
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `PseudoEmetricSpace [`α]) "]")]
   (Term.typeSpec ":" (Term.app `ParacompactSpace [`α])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.classical "classical") [])
       (group
        (Tactic.have''
         "have"
         [`pow_pos []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
            ","
            («term_<_»
             (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
             "<"
             (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`k] [])]
           "=>"
           (Term.app
            `Ennreal.pow_pos
            [(Term.app (Term.proj `Ennreal.inv_pos "." (fieldIdx "2")) [`Ennreal.two_ne_top]) (Term.hole "_")]))))
        [])
       (group
        (Tactic.have''
         "have"
         [`hpow_le []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.implicitBinder "{" [`m `n] [":" (termℕ "ℕ")] "}")]
            ","
            (Term.arrow
             («term_≤_» `m "≤" `n)
             "→"
             («term_≤_»
              (Cardinal.SetTheory.Cardinal.«term_^_»
               (Term.paren
                "("
                [(Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                 [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
                ")")
               "^"
               `n)
              "≤"
              (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`m `n `h] [])]
           "=>"
           (Term.app
            `Ennreal.pow_le_pow_of_le_one
            [(Term.app (Term.proj `Ennreal.inv_le_one "." (fieldIdx "2")) [`ennreal.one_lt_two.le]) `h]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h2pow []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
              ","
              («term_=_»
               (Finset.Data.Finset.Fold.«term_*_»
                (numLit "2")
                "*"
                (Cardinal.SetTheory.Cardinal.«term_^_»
                 (Term.paren
                  "("
                  [(Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                   [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
                  ")")
                 "^"
                 (Init.Logic.«term_+_» `n "+" (numLit "1"))))
               "="
               (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intro "intro" [`n]) [])
                    (group
                     (Tactic.simp
                      "simp"
                      []
                      []
                      ["["
                       [(Tactic.simpLemma [] [] `pow_succₓ)
                        ","
                        (Tactic.simpLemma [] ["←"] `mul_assocₓ)
                        ","
                        (Tactic.simpLemma [] [] `Ennreal.mul_inv_cancel)]
                       "]"]
                      [])
                     [])])))
                [])]))))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`ι `s `ho `hcov] [])] "=>" (Term.hole "_")))]
          "⟩"))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `Union_eq_univ_iff)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`hcov] []))])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `LinearOrderₓ [`ι]))]
           ":="
           (Term.app `linearOrderOfSTO' [`WellOrderingRel]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`wf []]
           [(Term.typeSpec
             ":"
             (Term.app
              `WellFounded
              [(Term.paren
                "("
                [(«term_<_» (Term.cdot "·") "<" (Term.cdot "·"))
                 [(Term.typeAscription ":" (Term.arrow `ι "→" (Term.arrow `ι "→" (Term.prop "Prop"))))]]
                ")")]))]
           ":="
           (Term.app (Term.explicit "@" `IsWellOrder.wf) [`ι `WellOrderingRel (Term.hole "_")]))))
        [])
       (group
        (Tactic.set
         "set"
         `ind
         [":" (Term.arrow `α "→" `ι)]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.app
            `wf.min
            [(Set.«term{_|_}»
              "{"
              (Mathlib.ExtendedBinder.extBinder `i [":" `ι])
              "|"
              (Init.Core.«term_∈_» `x " ∈ " (Term.app `s [`i]))
              "}")
             (Term.app `hcov [`x])])))
         [])
        [])
       (group
        (Tactic.have''
         "have"
         [`mem_ind []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.simpleBinder [`x] [])]
            ","
            (Init.Core.«term_∈_» `x " ∈ " (Term.app `s [(Term.app `ind [`x])]))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.app `wf.min_mem [(Term.hole "_") (Term.app `hcov [`x])]))))
        [])
       (group
        (Tactic.have''
         "have"
         [`nmem_of_lt_ind []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.implicitBinder "{" [`x `i] [] "}")]
            ","
            (Term.arrow
             («term_<_» `i "<" (Term.app `ind [`x]))
             "→"
             (Init.Core.«term_∉_» `x " ∉ " (Term.app `s [`i])))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x `i `hlt `hxi] [])]
           "=>"
           (Term.app `wf.not_lt_min [(Term.hole "_") (Term.app `hcov [`x]) `hxi `hlt]))))
        [])
       (group
        (Tactic.set
         "set"
         `D
         [":" (Term.arrow (termℕ "ℕ") "→" (Term.arrow `ι "→" (Term.app `Set [`α])))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`n] [])]
           "=>"
           (Term.app
            `Nat.strongRecOn'
            [`n
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`n `D' `i] [])]
               "=>"
               (Set.Data.Set.Lattice.«term⋃_,_»
                "⋃"
                (Lean.explicitBinders
                 [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" `α ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent `hxs)]
                   ":"
                   («term_=_» (Term.app `ind [`x]) "=" `i)
                   ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent `hb)]
                   ":"
                   (Init.Core.«term_⊆_»
                    (Term.app
                     `ball
                     [`x
                      (Finset.Data.Finset.Fold.«term_*_»
                       (numLit "3")
                       "*"
                       (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))])
                    " ⊆ "
                    (Term.app `s [`i]))
                   ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent `hlt)]
                   ":"
                   (Term.forall
                    "∀"
                    []
                    ","
                    (Mathlib.ExtendedBinder.«term∀___,_»
                     "∀"
                     `m
                     (Mathlib.ExtendedBinder.«binderTerm<_» "<" `n)
                     ","
                     (Term.forall
                      "∀"
                      [(Term.simpleBinder [`j] [(Term.typeSpec ":" `ι)])]
                      ","
                      (Init.Core.«term_∉_» `x " ∉ " (Term.app `D' [`m («term‹_›» "‹" (Term.hole "_") "›") `j])))))
                   ")")])
                ", "
                (Term.app
                 `ball
                 [`x (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)]))))])))
         [])
        [])
       (group
        (Tactic.have''
         "have"
         [`Dn []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.simpleBinder [`n `i] [])]
            ","
            («term_=_»
             (Term.app `D [`n `i])
             "="
             (Set.Data.Set.Lattice.«term⋃_,_»
              "⋃"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" `α ")")
                (Lean.bracketedExplicitBinders
                 "("
                 [(Lean.binderIdent `hxs)]
                 ":"
                 («term_=_» (Term.app `ind [`x]) "=" `i)
                 ")")
                (Lean.bracketedExplicitBinders
                 "("
                 [(Lean.binderIdent `hb)]
                 ":"
                 (Init.Core.«term_⊆_»
                  (Term.app
                   `ball
                   [`x
                    (Finset.Data.Finset.Fold.«term_*_»
                     (numLit "3")
                     "*"
                     (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))])
                  " ⊆ "
                  (Term.app `s [`i]))
                 ")")
                (Lean.bracketedExplicitBinders
                 "("
                 [(Lean.binderIdent `hlt)]
                 ":"
                 (Term.forall
                  "∀"
                  []
                  ","
                  (Mathlib.ExtendedBinder.«term∀___,_»
                   "∀"
                   `m
                   (Mathlib.ExtendedBinder.«binderTerm<_» "<" `n)
                   ","
                   (Term.forall
                    "∀"
                    [(Term.simpleBinder [`j] [(Term.typeSpec ":" `ι)])]
                    ","
                    (Init.Core.«term_∉_» `x " ∉ " (Term.app `D [`m `j])))))
                 ")")])
              ", "
              (Term.app
               `ball
               [`x (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)])))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`n `s] [])]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `D)] "]"] []) [])
               (group
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.strong_rec_on_beta')] "]") [])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`memD []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.implicitBinder "{" [`n `i `y] [] "}")]
              ","
              («term_↔_»
               (Init.Core.«term_∈_» `y " ∈ " (Term.app `D [`n `i]))
               "↔"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders
                 [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent `hi)]
                   ":"
                   («term_=_» (Term.app `ind [`x]) "=" `i)
                   ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent `hb)]
                   ":"
                   (Init.Core.«term_⊆_»
                    (Term.app
                     `ball
                     [`x
                      (Finset.Data.Finset.Fold.«term_*_»
                       (numLit "3")
                       "*"
                       (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))])
                    " ⊆ "
                    (Term.app `s [`i]))
                   ")")
                  (Lean.bracketedExplicitBinders
                   "("
                   [(Lean.binderIdent `hlt)]
                   ":"
                   (Term.forall
                    "∀"
                    []
                    ","
                    (Mathlib.ExtendedBinder.«term∀___,_»
                     "∀"
                     `m
                     (Mathlib.ExtendedBinder.«binderTerm<_» "<" `n)
                     ","
                     (Term.forall
                      "∀"
                      [(Term.simpleBinder [`j] [(Term.typeSpec ":" `ι)])]
                      ","
                      (Init.Core.«term_∉_» `x " ∉ " (Term.app `D [`m `j])))))
                   ")")])
                ","
                («term_<_»
                 (Term.app `edist [`y `x])
                 "<"
                 (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`n `i `y]) [])
               (group
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Dn [`n `i]))] "]") [])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `mem_Union) "," (Tactic.simpLemma [] [] `mem_ball)] "]"]
                 [])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`Dcov []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x] [])]
              ","
              («term∃_,_»
               "∃"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n) (Lean.binderIdent `i)] []))
               ","
               (Init.Core.«term_∈_» `x " ∈ " (Term.app `D [`n `i])))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`x]) [])
               (group
                (Tactic.obtain
                 "obtain"
                 [(Tactic.rcasesPatMed
                   [(Tactic.rcasesPat.tuple
                     "⟨"
                     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
                     "⟩")])]
                 [":"
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
                   ","
                   (Init.Core.«term_⊆_»
                    (Term.app
                     `ball
                     [`x
                      (Finset.Data.Finset.Fold.«term_*_»
                       (numLit "3")
                       "*"
                       (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))])
                    " ⊆ "
                    (Term.app `s [(Term.app `ind [`x])])))]
                 [])
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget
                        []
                        (Term.app
                         (Term.proj `is_open_iff "." (fieldIdx "1"))
                         [(«term_$__» `ho "$" (Term.app `ind [`x])) `x (Term.app `mem_ind [`x])]))]
                      ["with"
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε0)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hε)]) [])]
                        "⟩")])
                     [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec ":" («term_<_» (numLit "0") "<" («term_/_» `ε "/" (numLit "3"))))]
                        ":="
                        (Term.app
                         (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
                         [(Term.anonymousCtor "⟨" [`ε0.lt.ne' "," `Ennreal.coe_ne_top] "⟩")]))))
                     [])
                    (group
                     (Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] (Term.app `Ennreal.exists_inv_two_pow_lt [`this.ne']))]
                      ["with"
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
                        "⟩")])
                     [])
                    (group
                     (Tactic.refine'
                      "refine'"
                      (Term.anonymousCtor
                       "⟨"
                       [`n "," (Term.app `subset.trans [(Term.app `ball_subset_ball [(Term.hole "_")]) `hε])]
                       "⟩"))
                     [])
                    (group
                     (Tactic.simpa
                      "simpa"
                      []
                      ["only"]
                      ["[" [(Tactic.simpLemma [] [] `div_eq_mul_inv) "," (Tactic.simpLemma [] [] `mul_commₓ)] "]"]
                      []
                      ["using" (Term.proj (Term.app `Ennreal.mul_lt_of_lt_div [`hn]) "." `le)])
                     [])])))
                [])
               (group (byContra "by_contra" [`h]) [])
               (group (Tactic.pushNeg "push_neg" [(Tactic.location "at" (Tactic.locationHyp [`h] []))]) [])
               (group (Tactic.apply "apply" (Term.app `h [`n (Term.app `ind [`x])])) [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj `memD "." (fieldIdx "2"))
                  [(Term.anonymousCtor
                    "⟨"
                    [`x
                     ","
                     `rfl
                     ","
                     `hn
                     ","
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") (Term.hole "_")] [])]
                       "=>"
                       (Term.app `h [(Term.hole "_") (Term.hole "_")])))
                     ","
                     (Term.app `mem_ball_self [(Term.app `pow_pos [(Term.hole "_")])])]
                    "⟩")]))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`Dopen []]
           [(Term.typeSpec
             ":"
             (Term.forall "∀" [(Term.simpleBinder [`n `i] [])] "," (Term.app `IsOpen [(Term.app `D [`n `i])])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`n `i]) [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dn)] "]") []) [])
               (group
                (tacticIterate____
                 "iterate"
                 [(numLit "4")]
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       `is_open_Union
                       [(Term.fun
                         "fun"
                         (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.hole "_")))]))
                     [])])))
                [])
               (group (Tactic.exact "exact" `is_open_ball) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`HDS []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n `i] [])]
              ","
              (Init.Core.«term_⊆_» (Term.app `D [`n `i]) " ⊆ " (Term.app `s [`i]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`n `s `x]) [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `memD)] "]") []) [])
               (group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hsub)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyx)]) [])]
                    "⟩"))]
                 [])
                [])
               (group
                (Tactic.refine' "refine'" (Term.app `hsub [(Term.app `lt_of_lt_of_leₓ [`hyx (Term.hole "_")])]))
                [])
               (group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_=_»
                    (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)
                    "="
                    (Finset.Data.Finset.Fold.«term_*_»
                     (numLit "1")
                     "*"
                     (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)))
                   ":="
                   (Term.proj (Term.app `one_mulₓ [(Term.hole "_")]) "." `symm))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    (Finset.Data.Finset.Fold.«term_*_»
                     (numLit "3")
                     "*"
                     (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)))
                   ":="
                   (Term.app `Ennreal.mul_le_mul [(Term.hole "_") `le_rfl]))])
                [])
               (group
                (Tactic.have''
                 "have"
                 []
                 [(Term.typeSpec
                   ":"
                   («term_≤_»
                    (Term.paren
                     "("
                     [(Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (termℕ "ℕ"))]] ")")
                      [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
                     ")")
                    "≤"
                    (Term.paren "(" [(numLit "3") [(Term.typeAscription ":" (termℕ "ℕ"))]] ")")))])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj `Ennreal.coe_nat_le_coe_nat "." (fieldIdx "2"))
                  [(Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.normNum1 "norm_num1" []) [])])))]))
                [])
               (group (Tactic.exactModCast "exact_mod_cast" `this) [])]))))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(«term_×_» (termℕ "ℕ") "×" `ι)
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`ni] [])]
             "=>"
             (Term.app `D [(Term.proj `ni "." (fieldIdx "1")) (Term.proj `ni "." (fieldIdx "2"))])))
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [(Term.hole "_")] [])]
             "=>"
             (Term.app `Dopen [(Term.hole "_") (Term.hole "_")])))
           ","
           (Term.hole "_")
           ","
           (Term.hole "_")
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`ni] [])]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.proj `ni "." (fieldIdx "2")) "," (Term.app `HDS [(Term.hole "_") (Term.hole "_")])]
              "⟩")))]
          "⟩"))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj `Union_eq_univ_iff "." (fieldIdx "2"))
               [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))]))
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `Dcov [`x]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`n "," `i] "⟩") "," `h] "⟩"))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`x]) [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `Dcov [`x]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.have''
              "have"
              []
              [(Term.typeSpec
                ":"
                (Init.Core.«term_∈_» (Term.app `D [`n `i]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app `IsOpen.mem_nhds [(Term.app `Dopen [(Term.hole "_") (Term.hole "_")]) `hn]))
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `nhds_basis_uniformity [`uniformity_basis_edist_inv_two_pow]) "." `mem_iff)
                  "."
                  (fieldIdx "1"))
                 [`this]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                 ","
                 (Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hsub)])
                  [":"
                   (Init.Core.«term_⊆_»
                    (Term.app
                     `ball
                     [`x (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k)])
                    " ⊆ "
                    (Term.app `D [`n `i]))])]
                "⟩")])
             [])
            (group
             (Tactic.set
              "set"
              `B
              []
              ":="
              (Term.app
               `ball
               [`x
                (Cardinal.SetTheory.Cardinal.«term_^_»
                 (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                 "^"
                 (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))])
              [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`B
                ","
                (Term.app `ball_mem_nhds [(Term.hole "_") (Term.app `pow_pos [(Term.hole "_")])])
                ","
                (Term.hole "_")]
               "⟩"))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Hgt []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   []
                   ","
                   (Mathlib.ExtendedBinder.«term∀___,_»
                    "∀"
                    `m
                    (Mathlib.ExtendedBinder.«binderTerm≥_»
                     "≥"
                     (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))
                    ","
                    (Term.forall
                     "∀"
                     [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
                     ","
                     (Term.app `Disjoint [(Term.app `D [`m `i]) `B])))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rintro
                      "rintro"
                      [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m))
                       (Tactic.rintroPat.one (Tactic.rcasesPat.one `hm))
                       (Tactic.rintroPat.one (Tactic.rcasesPat.one `i))
                       (Tactic.rintroPat.one (Tactic.rcasesPat.one `y))
                       (Tactic.rintroPat.one
                        (Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hym)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyx)]) [])]
                         "⟩"))]
                      [])
                     [])
                    (group
                     (Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hym]))]
                      ["with"
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzi)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `H)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hz)]) [])]
                        "⟩")])
                     [])
                    (group
                     (Tactic.have''
                      "have"
                      []
                      [(Term.typeSpec
                        ":"
                        (Init.Core.«term_∉_»
                         `z
                         " ∉ "
                         (Term.app
                          `ball
                          [`x
                           (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k)])))])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`hz] [])]
                        "=>"
                        (Term.app
                         `H
                         [`n
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
                          `i
                          (Term.app `hsub [`hz])]))))
                     [])
                    (group (Tactic.apply "apply" `this) [])
                    (group
                     (tacticCalc_
                      "calc"
                      [(calcStep
                        («term_≤_»
                         (Term.app `edist [`z `x])
                         "≤"
                         (Init.Logic.«term_+_» (Term.app `edist [`y `z]) "+" (Term.app `edist [`y `x])))
                        ":="
                        (Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                       (calcStep
                        («term_<_»
                         (Term.hole "_")
                         "<"
                         (Init.Logic.«term_+_»
                          (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                          "+"
                          (Cardinal.SetTheory.Cardinal.«term_^_»
                           (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                           "^"
                           (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))))
                        ":="
                        (Term.app `Ennreal.add_lt_add [`hz `hyx]))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Init.Logic.«term_+_»
                          (Cardinal.SetTheory.Cardinal.«term_^_»
                           (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                           "^"
                           (Init.Logic.«term_+_» `k "+" (numLit "1")))
                          "+"
                          (Cardinal.SetTheory.Cardinal.«term_^_»
                           (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                           "^"
                           (Init.Logic.«term_+_» `k "+" (numLit "1")))))
                        ":="
                        (Term.app
                         `add_le_add
                         [(«term_$__»
                           `hpow_le
                           "$"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))
                          («term_$__»
                           `hpow_le
                           "$"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))]))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `two_mul) "," (Tactic.rwRule [] `h2pow)] "]")
                              [])
                             [])]))))])
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Hle []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   []
                   ","
                   (Mathlib.ExtendedBinder.«term∀___,_»
                    "∀"
                    `m
                    (Mathlib.ExtendedBinder.«binderTerm≤_» "≤" (Init.Logic.«term_+_» `n "+" `k))
                    ","
                    (Term.forall
                     "∀"
                     []
                     ","
                     (Term.app
                      `Set.Subsingleton
                      [(Set.«term{_|_}»
                        "{"
                        `j
                        "|"
                        (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `j]) " ∩ " `B) "." `Nonempty)
                        "}")])))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rintro
                      "rintro"
                      [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m))
                       (Tactic.rintroPat.one (Tactic.rcasesPat.one `hm))
                       (Tactic.rintroPat.one (Tactic.rcasesPat.one `j₁))
                       (Tactic.rintroPat.one
                        (Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyD)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyB)]) [])]
                         "⟩"))
                       (Tactic.rintroPat.one (Tactic.rcasesPat.one `j₂))
                       (Tactic.rintroPat.one
                        (Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzD)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzB)]) [])]
                         "⟩"))]
                      [])
                     [])
                    (group (byContra "by_contra" [`h]) [])
                    (group
                     (Tactic.wlog
                      "wlog"
                      []
                      [`h]
                      [":" («term_<_» `j₁ "<" `j₂)]
                      [":=" (Term.app `Ne.lt_or_lt [`h])]
                      ["using" [[`j₁ `j₂ `y `z] "," [`j₂ `j₁ `z `y]]])
                     [])
                    (group
                     (Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hyD]))]
                      ["with"
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y')]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hsuby)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdisty)]) [])]
                        "⟩")])
                     [])
                    (group
                     (Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hzD]))]
                      ["with"
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z')]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdistz)]) [])]
                        "⟩")])
                     [])
                    (group
                     (Tactic.suffices'
                      "suffices"
                      []
                      [(Term.typeSpec
                        ":"
                        («term_<_»
                         (Term.app `edist [`z' `y'])
                         "<"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (numLit "3")
                          "*"
                          (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m))))])
                     [])
                    (group (Tactic.exact "exact" (Term.app `nmem_of_lt_ind [`h (Term.app `hsuby [`this])])) [])
                    (group
                     (tacticCalc_
                      "calc"
                      [(calcStep
                        («term_≤_»
                         (Term.app `edist [`z' `y'])
                         "≤"
                         (Init.Logic.«term_+_» (Term.app `edist [`z' `x]) "+" (Term.app `edist [`x `y'])))
                        ":="
                        (Term.app `edist_triangle [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Init.Logic.«term_+_»
                          (Init.Logic.«term_+_» (Term.app `edist [`z `z']) "+" (Term.app `edist [`z `x]))
                          "+"
                          (Init.Logic.«term_+_» (Term.app `edist [`y `x]) "+" (Term.app `edist [`y `y']))))
                        ":="
                        (Term.app
                         `add_le_add
                         [(Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                          (Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
                       (calcStep
                        («term_<_»
                         (Term.hole "_")
                         "<"
                         (Init.Logic.«term_+_»
                          (Init.Logic.«term_+_»
                           (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                           "+"
                           (Cardinal.SetTheory.Cardinal.«term_^_»
                            (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                            "^"
                            (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1"))))
                          "+"
                          (Init.Logic.«term_+_»
                           (Cardinal.SetTheory.Cardinal.«term_^_»
                            (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                            "^"
                            (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))
                           "+"
                           (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.applyRules "apply_rules" [] "[" [`Ennreal.add_lt_add] "]" []) [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Finset.Data.Finset.Fold.«term_*_»
                          (numLit "2")
                          "*"
                          (Init.Logic.«term_+_»
                           (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                           "+"
                           (Cardinal.SetTheory.Cardinal.«term_^_»
                            (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                            "^"
                            (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1"))))))
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
                              ["[" [(Tactic.simpLemma [] [] `two_mul) "," (Tactic.simpLemma [] [] `add_commₓ)] "]"]
                              [])
                             [])]))))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (numLit "2")
                          "*"
                          (Init.Logic.«term_+_»
                           (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                           "+"
                           (Cardinal.SetTheory.Cardinal.«term_^_»
                            (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                            "^"
                            (Init.Logic.«term_+_» `m "+" (numLit "1"))))))
                        ":="
                        («term_$__»
                         (Term.app `Ennreal.mul_le_mul [`le_rfl])
                         "$"
                         («term_$__»
                          (Term.app `add_le_add [`le_rfl])
                          "$"
                          (Term.app `hpow_le [(Term.app `add_le_add [`hm `le_rfl])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Finset.Data.Finset.Fold.«term_*_»
                          (numLit "3")
                          "*"
                          (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)))
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
                               [(Tactic.rwRule [] `mul_addₓ)
                                ","
                                (Tactic.rwRule [] `h2pow)
                                ","
                                (Tactic.rwRule [] `bit1)
                                ","
                                (Tactic.rwRule [] `add_mulₓ)
                                ","
                                (Tactic.rwRule [] `one_mulₓ)]
                               "]")
                              [])
                             [])]))))])
                     [])]))))))
             [])
            (group
             (Tactic.have''
              "have"
              []
              [(Term.typeSpec
                ":"
                (Term.proj
                 (Set.Data.Set.Lattice.«term⋃_,_»
                  "⋃"
                  (Lean.explicitBinders
                   [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `m)] ":" (Term.hole "_") ")")
                    (Lean.bracketedExplicitBinders
                     "("
                     [(Lean.binderIdent "_")]
                     ":"
                     («term_≤_» `m "≤" (Init.Logic.«term_+_» `n "+" `k))
                     ")")
                    (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
                    (Lean.bracketedExplicitBinders
                     "("
                     [(Lean.binderIdent "_")]
                     ":"
                     (Init.Core.«term_∈_»
                      `i
                      " ∈ "
                      (Set.«term{_|_}»
                       "{"
                       (Mathlib.ExtendedBinder.extBinder `i [":" `ι])
                       "|"
                       (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `i]) " ∩ " `B) "." `Nonempty)
                       "}"))
                     ")")])
                  ", "
                  (Set.«term{_}» "{" [(Term.paren "(" [`m [(Term.tupleTail "," [`i])]] ")")] "}"))
                 "."
                 `Finite))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.app `finite_le_nat [(Term.hole "_")]) "." `bUnion)
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`i `hi] [])]
                  "=>"
                  (Term.app
                   (Term.proj (Term.proj (Term.app `Hle [`i `hi]) "." `Finite) "." `bUnion)
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                      "=>"
                      (Term.app `finite_singleton [(Term.hole "_")])))])))]))
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               `this.subset
               [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`I `hI] [])] "=>" (Term.hole "_")))]))
             [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_Union)] "]"] []) [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.proj `I "." (fieldIdx "1"))
                ","
                (Term.hole "_")
                ","
                (Term.proj `I "." (fieldIdx "2"))
                ","
                `hI
                ","
                `prod.mk.eta.symm]
               "⟩"))
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj `not_ltₓ "." (fieldIdx "1"))
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`hlt] [])]
                  "=>"
                  (Term.app
                   `Hgt
                   [(Term.proj `I "." (fieldIdx "1")) `hlt (Term.proj `I "." (fieldIdx "2")) `hI.some_spec])))]))
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.classical "classical") [])
      (group
       (Tactic.have''
        "have"
        [`pow_pos []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
           ","
           («term_<_»
            (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
            "<"
            (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k] [])]
          "=>"
          (Term.app
           `Ennreal.pow_pos
           [(Term.app (Term.proj `Ennreal.inv_pos "." (fieldIdx "2")) [`Ennreal.two_ne_top]) (Term.hole "_")]))))
       [])
      (group
       (Tactic.have''
        "have"
        [`hpow_le []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.implicitBinder "{" [`m `n] [":" (termℕ "ℕ")] "}")]
           ","
           (Term.arrow
            («term_≤_» `m "≤" `n)
            "→"
            («term_≤_»
             (Cardinal.SetTheory.Cardinal.«term_^_»
              (Term.paren
               "("
               [(Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
               ")")
              "^"
              `n)
             "≤"
             (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`m `n `h] [])]
          "=>"
          (Term.app
           `Ennreal.pow_le_pow_of_le_one
           [(Term.app (Term.proj `Ennreal.inv_le_one "." (fieldIdx "2")) [`ennreal.one_lt_two.le]) `h]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h2pow []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
             ","
             («term_=_»
              (Finset.Data.Finset.Fold.«term_*_»
               (numLit "2")
               "*"
               (Cardinal.SetTheory.Cardinal.«term_^_»
                (Term.paren
                 "("
                 [(Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                  [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
                 ")")
                "^"
                (Init.Logic.«term_+_» `n "+" (numLit "1"))))
              "="
              (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`n]) [])
                   (group
                    (Tactic.simp
                     "simp"
                     []
                     []
                     ["["
                      [(Tactic.simpLemma [] [] `pow_succₓ)
                       ","
                       (Tactic.simpLemma [] ["←"] `mul_assocₓ)
                       ","
                       (Tactic.simpLemma [] [] `Ennreal.mul_inv_cancel)]
                      "]"]
                     [])
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`ι `s `ho `hcov] [])] "=>" (Term.hole "_")))]
         "⟩"))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Union_eq_univ_iff)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`hcov] []))])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this'
          []
          [(Term.typeSpec ":" (Term.app `LinearOrderₓ [`ι]))]
          ":="
          (Term.app `linearOrderOfSTO' [`WellOrderingRel]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`wf []]
          [(Term.typeSpec
            ":"
            (Term.app
             `WellFounded
             [(Term.paren
               "("
               [(«term_<_» (Term.cdot "·") "<" (Term.cdot "·"))
                [(Term.typeAscription ":" (Term.arrow `ι "→" (Term.arrow `ι "→" (Term.prop "Prop"))))]]
               ")")]))]
          ":="
          (Term.app (Term.explicit "@" `IsWellOrder.wf) [`ι `WellOrderingRel (Term.hole "_")]))))
       [])
      (group
       (Tactic.set
        "set"
        `ind
        [":" (Term.arrow `α "→" `ι)]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.app
           `wf.min
           [(Set.«term{_|_}»
             "{"
             (Mathlib.ExtendedBinder.extBinder `i [":" `ι])
             "|"
             (Init.Core.«term_∈_» `x " ∈ " (Term.app `s [`i]))
             "}")
            (Term.app `hcov [`x])])))
        [])
       [])
      (group
       (Tactic.have''
        "have"
        [`mem_ind []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`x] [])]
           ","
           (Init.Core.«term_∈_» `x " ∈ " (Term.app `s [(Term.app `ind [`x])]))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.app `wf.min_mem [(Term.hole "_") (Term.app `hcov [`x])]))))
       [])
      (group
       (Tactic.have''
        "have"
        [`nmem_of_lt_ind []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.implicitBinder "{" [`x `i] [] "}")]
           ","
           (Term.arrow
            («term_<_» `i "<" (Term.app `ind [`x]))
            "→"
            (Init.Core.«term_∉_» `x " ∉ " (Term.app `s [`i])))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x `i `hlt `hxi] [])]
          "=>"
          (Term.app `wf.not_lt_min [(Term.hole "_") (Term.app `hcov [`x]) `hxi `hlt]))))
       [])
      (group
       (Tactic.set
        "set"
        `D
        [":" (Term.arrow (termℕ "ℕ") "→" (Term.arrow `ι "→" (Term.app `Set [`α])))]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`n] [])]
          "=>"
          (Term.app
           `Nat.strongRecOn'
           [`n
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`n `D' `i] [])]
              "=>"
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" `α ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent `hxs)]
                  ":"
                  («term_=_» (Term.app `ind [`x]) "=" `i)
                  ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent `hb)]
                  ":"
                  (Init.Core.«term_⊆_»
                   (Term.app
                    `ball
                    [`x
                     (Finset.Data.Finset.Fold.«term_*_»
                      (numLit "3")
                      "*"
                      (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))])
                   " ⊆ "
                   (Term.app `s [`i]))
                  ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent `hlt)]
                  ":"
                  (Term.forall
                   "∀"
                   []
                   ","
                   (Mathlib.ExtendedBinder.«term∀___,_»
                    "∀"
                    `m
                    (Mathlib.ExtendedBinder.«binderTerm<_» "<" `n)
                    ","
                    (Term.forall
                     "∀"
                     [(Term.simpleBinder [`j] [(Term.typeSpec ":" `ι)])]
                     ","
                     (Init.Core.«term_∉_» `x " ∉ " (Term.app `D' [`m («term‹_›» "‹" (Term.hole "_") "›") `j])))))
                  ")")])
               ", "
               (Term.app
                `ball
                [`x (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)]))))])))
        [])
       [])
      (group
       (Tactic.have''
        "have"
        [`Dn []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`n `i] [])]
           ","
           («term_=_»
            (Term.app `D [`n `i])
            "="
            (Set.Data.Set.Lattice.«term⋃_,_»
             "⋃"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" `α ")")
               (Lean.bracketedExplicitBinders
                "("
                [(Lean.binderIdent `hxs)]
                ":"
                («term_=_» (Term.app `ind [`x]) "=" `i)
                ")")
               (Lean.bracketedExplicitBinders
                "("
                [(Lean.binderIdent `hb)]
                ":"
                (Init.Core.«term_⊆_»
                 (Term.app
                  `ball
                  [`x
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "3")
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))])
                 " ⊆ "
                 (Term.app `s [`i]))
                ")")
               (Lean.bracketedExplicitBinders
                "("
                [(Lean.binderIdent `hlt)]
                ":"
                (Term.forall
                 "∀"
                 []
                 ","
                 (Mathlib.ExtendedBinder.«term∀___,_»
                  "∀"
                  `m
                  (Mathlib.ExtendedBinder.«binderTerm<_» "<" `n)
                  ","
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder [`j] [(Term.typeSpec ":" `ι)])]
                   ","
                   (Init.Core.«term_∉_» `x " ∉ " (Term.app `D [`m `j])))))
                ")")])
             ", "
             (Term.app
              `ball
              [`x (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)])))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`n `s] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `D)] "]"] []) [])
              (group
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nat.strong_rec_on_beta')] "]") [])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`memD []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.implicitBinder "{" [`n `i `y] [] "}")]
             ","
             («term_↔_»
              (Init.Core.«term_∈_» `y " ∈ " (Term.app `D [`n `i]))
              "↔"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `x)] ":" (Term.hole "_") ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent `hi)]
                  ":"
                  («term_=_» (Term.app `ind [`x]) "=" `i)
                  ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent `hb)]
                  ":"
                  (Init.Core.«term_⊆_»
                   (Term.app
                    `ball
                    [`x
                     (Finset.Data.Finset.Fold.«term_*_»
                      (numLit "3")
                      "*"
                      (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))])
                   " ⊆ "
                   (Term.app `s [`i]))
                  ")")
                 (Lean.bracketedExplicitBinders
                  "("
                  [(Lean.binderIdent `hlt)]
                  ":"
                  (Term.forall
                   "∀"
                   []
                   ","
                   (Mathlib.ExtendedBinder.«term∀___,_»
                    "∀"
                    `m
                    (Mathlib.ExtendedBinder.«binderTerm<_» "<" `n)
                    ","
                    (Term.forall
                     "∀"
                     [(Term.simpleBinder [`j] [(Term.typeSpec ":" `ι)])]
                     ","
                     (Init.Core.«term_∉_» `x " ∉ " (Term.app `D [`m `j])))))
                  ")")])
               ","
               («term_<_»
                (Term.app `edist [`y `x])
                "<"
                (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n `i `y]) [])
              (group
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Dn [`n `i]))] "]") [])
               [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `mem_Union) "," (Tactic.simpLemma [] [] `mem_ball)] "]"]
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`Dcov []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x] [])]
             ","
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n) (Lean.binderIdent `i)] []))
              ","
              (Init.Core.«term_∈_» `x " ∈ " (Term.app `D [`n `i])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`x]) [])
              (group
               (Tactic.obtain
                "obtain"
                [(Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
                    "⟩")])]
                [":"
                 («term∃_,_»
                  "∃"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
                  ","
                  (Init.Core.«term_⊆_»
                   (Term.app
                    `ball
                    [`x
                     (Finset.Data.Finset.Fold.«term_*_»
                      (numLit "3")
                      "*"
                      (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n))])
                   " ⊆ "
                   (Term.app `s [(Term.app `ind [`x])])))]
                [])
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget
                       []
                       (Term.app
                        (Term.proj `is_open_iff "." (fieldIdx "1"))
                        [(«term_$__» `ho "$" (Term.app `ind [`x])) `x (Term.app `mem_ind [`x])]))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε0)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hε)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec ":" («term_<_» (numLit "0") "<" («term_/_» `ε "/" (numLit "3"))))]
                       ":="
                       (Term.app
                        (Term.proj `Ennreal.div_pos_iff "." (fieldIdx "2"))
                        [(Term.anonymousCtor "⟨" [`ε0.lt.ne' "," `Ennreal.coe_ne_top] "⟩")]))))
                    [])
                   (group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] (Term.app `Ennreal.exists_inv_two_pow_lt [`this.ne']))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.refine'
                     "refine'"
                     (Term.anonymousCtor
                      "⟨"
                      [`n "," (Term.app `subset.trans [(Term.app `ball_subset_ball [(Term.hole "_")]) `hε])]
                      "⟩"))
                    [])
                   (group
                    (Tactic.simpa
                     "simpa"
                     []
                     ["only"]
                     ["[" [(Tactic.simpLemma [] [] `div_eq_mul_inv) "," (Tactic.simpLemma [] [] `mul_commₓ)] "]"]
                     []
                     ["using" (Term.proj (Term.app `Ennreal.mul_lt_of_lt_div [`hn]) "." `le)])
                    [])])))
               [])
              (group (byContra "by_contra" [`h]) [])
              (group (Tactic.pushNeg "push_neg" [(Tactic.location "at" (Tactic.locationHyp [`h] []))]) [])
              (group (Tactic.apply "apply" (Term.app `h [`n (Term.app `ind [`x])])) [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `memD "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [`x
                    ","
                    `rfl
                    ","
                    `hn
                    ","
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") (Term.hole "_")] [])]
                      "=>"
                      (Term.app `h [(Term.hole "_") (Term.hole "_")])))
                    ","
                    (Term.app `mem_ball_self [(Term.app `pow_pos [(Term.hole "_")])])]
                   "⟩")]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`Dopen []]
          [(Term.typeSpec
            ":"
            (Term.forall "∀" [(Term.simpleBinder [`n `i] [])] "," (Term.app `IsOpen [(Term.app `D [`n `i])])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n `i]) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Dn)] "]") []) [])
              (group
               (tacticIterate____
                "iterate"
                [(numLit "4")]
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `is_open_Union
                      [(Term.fun
                        "fun"
                        (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.hole "_")))]))
                    [])])))
               [])
              (group (Tactic.exact "exact" `is_open_ball) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`HDS []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n `i] [])]
             ","
             (Init.Core.«term_⊆_» (Term.app `D [`n `i]) " ⊆ " (Term.app `s [`i]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n `s `x]) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `memD)] "]") []) [])
              (group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hsub)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyx)]) [])]
                   "⟩"))]
                [])
               [])
              (group
               (Tactic.refine' "refine'" (Term.app `hsub [(Term.app `lt_of_lt_of_leₓ [`hyx (Term.hole "_")])]))
               [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_=_»
                   (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)
                   "="
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "1")
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)))
                  ":="
                  (Term.proj (Term.app `one_mulₓ [(Term.hole "_")]) "." `symm))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "3")
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `n)))
                  ":="
                  (Term.app `Ennreal.mul_le_mul [(Term.hole "_") `le_rfl]))])
               [])
              (group
               (Tactic.have''
                "have"
                []
                [(Term.typeSpec
                  ":"
                  («term_≤_»
                   (Term.paren
                    "("
                    [(Term.paren "(" [(numLit "1") [(Term.typeAscription ":" (termℕ "ℕ"))]] ")")
                     [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
                    ")")
                   "≤"
                   (Term.paren "(" [(numLit "3") [(Term.typeAscription ":" (termℕ "ℕ"))]] ")")))])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `Ennreal.coe_nat_le_coe_nat "." (fieldIdx "2"))
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.normNum1 "norm_num1" []) [])])))]))
               [])
              (group (Tactic.exactModCast "exact_mod_cast" `this) [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(«term_×_» (termℕ "ℕ") "×" `ι)
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`ni] [])]
            "=>"
            (Term.app `D [(Term.proj `ni "." (fieldIdx "1")) (Term.proj `ni "." (fieldIdx "2"))])))
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [(Term.hole "_")] [])]
            "=>"
            (Term.app `Dopen [(Term.hole "_") (Term.hole "_")])))
          ","
          (Term.hole "_")
          ","
          (Term.hole "_")
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`ni] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.proj `ni "." (fieldIdx "2")) "," (Term.app `HDS [(Term.hole "_") (Term.hole "_")])]
             "⟩")))]
         "⟩"))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj `Union_eq_univ_iff "." (fieldIdx "2"))
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `Dcov [`x]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.exact "exact" (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`n "," `i] "⟩") "," `h] "⟩"))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`x]) [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `Dcov [`x]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.have''
             "have"
             []
             [(Term.typeSpec
               ":"
               (Init.Core.«term_∈_» (Term.app `D [`n `i]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])))])
            [])
           (group
            (Tactic.exact "exact" (Term.app `IsOpen.mem_nhds [(Term.app `Dopen [(Term.hole "_") (Term.hole "_")]) `hn]))
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.proj (Term.app `nhds_basis_uniformity [`uniformity_basis_edist_inv_two_pow]) "." `mem_iff)
                 "."
                 (fieldIdx "1"))
                [`this]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                ","
                (Tactic.rcasesPatLo
                 (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hsub)])
                 [":"
                  (Init.Core.«term_⊆_»
                   (Term.app
                    `ball
                    [`x (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k)])
                   " ⊆ "
                   (Term.app `D [`n `i]))])]
               "⟩")])
            [])
           (group
            (Tactic.set
             "set"
             `B
             []
             ":="
             (Term.app
              `ball
              [`x
               (Cardinal.SetTheory.Cardinal.«term_^_»
                (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                "^"
                (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))])
             [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`B
               ","
               (Term.app `ball_mem_nhds [(Term.hole "_") (Term.app `pow_pos [(Term.hole "_")])])
               ","
               (Term.hole "_")]
              "⟩"))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Hgt []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  []
                  ","
                  (Mathlib.ExtendedBinder.«term∀___,_»
                   "∀"
                   `m
                   (Mathlib.ExtendedBinder.«binderTerm≥_»
                    "≥"
                    (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))
                   ","
                   (Term.forall
                    "∀"
                    [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
                    ","
                    (Term.app `Disjoint [(Term.app `D [`m `i]) `B])))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rintro
                     "rintro"
                     [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `hm))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `i))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `y))
                      (Tactic.rintroPat.one
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hym)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyx)]) [])]
                        "⟩"))]
                     [])
                    [])
                   (group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hym]))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzi)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `H)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hz)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.have''
                     "have"
                     []
                     [(Term.typeSpec
                       ":"
                       (Init.Core.«term_∉_»
                        `z
                        " ∉ "
                        (Term.app
                         `ball
                         [`x
                          (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k)])))])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`hz] [])]
                       "=>"
                       (Term.app
                        `H
                        [`n
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
                         `i
                         (Term.app `hsub [`hz])]))))
                    [])
                   (group (Tactic.apply "apply" `this) [])
                   (group
                    (tacticCalc_
                     "calc"
                     [(calcStep
                       («term_≤_»
                        (Term.app `edist [`z `x])
                        "≤"
                        (Init.Logic.«term_+_» (Term.app `edist [`y `z]) "+" (Term.app `edist [`y `x])))
                       ":="
                       (Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                      (calcStep
                       («term_<_»
                        (Term.hole "_")
                        "<"
                        (Init.Logic.«term_+_»
                         (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                         "+"
                         (Cardinal.SetTheory.Cardinal.«term_^_»
                          (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                          "^"
                          (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))))
                       ":="
                       (Term.app `Ennreal.add_lt_add [`hz `hyx]))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Init.Logic.«term_+_»
                         (Cardinal.SetTheory.Cardinal.«term_^_»
                          (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                          "^"
                          (Init.Logic.«term_+_» `k "+" (numLit "1")))
                         "+"
                         (Cardinal.SetTheory.Cardinal.«term_^_»
                          (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                          "^"
                          (Init.Logic.«term_+_» `k "+" (numLit "1")))))
                       ":="
                       (Term.app
                        `add_le_add
                        [(«term_$__»
                          `hpow_le
                          "$"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))
                         («term_$__»
                          `hpow_le
                          "$"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))]))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `two_mul) "," (Tactic.rwRule [] `h2pow)] "]")
                             [])
                            [])]))))])
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Hle []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  []
                  ","
                  (Mathlib.ExtendedBinder.«term∀___,_»
                   "∀"
                   `m
                   (Mathlib.ExtendedBinder.«binderTerm≤_» "≤" (Init.Logic.«term_+_» `n "+" `k))
                   ","
                   (Term.forall
                    "∀"
                    []
                    ","
                    (Term.app
                     `Set.Subsingleton
                     [(Set.«term{_|_}»
                       "{"
                       `j
                       "|"
                       (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `j]) " ∩ " `B) "." `Nonempty)
                       "}")])))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rintro
                     "rintro"
                     [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `hm))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `j₁))
                      (Tactic.rintroPat.one
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyD)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyB)]) [])]
                        "⟩"))
                      (Tactic.rintroPat.one (Tactic.rcasesPat.one `j₂))
                      (Tactic.rintroPat.one
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzD)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzB)]) [])]
                        "⟩"))]
                     [])
                    [])
                   (group (byContra "by_contra" [`h]) [])
                   (group
                    (Tactic.wlog
                     "wlog"
                     []
                     [`h]
                     [":" («term_<_» `j₁ "<" `j₂)]
                     [":=" (Term.app `Ne.lt_or_lt [`h])]
                     ["using" [[`j₁ `j₂ `y `z] "," [`j₂ `j₁ `z `y]]])
                    [])
                   (group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hyD]))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y')]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hsuby)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdisty)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hzD]))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z')]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdistz)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.suffices'
                     "suffices"
                     []
                     [(Term.typeSpec
                       ":"
                       («term_<_»
                        (Term.app `edist [`z' `y'])
                        "<"
                        (Finset.Data.Finset.Fold.«term_*_»
                         (numLit "3")
                         "*"
                         (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m))))])
                    [])
                   (group (Tactic.exact "exact" (Term.app `nmem_of_lt_ind [`h (Term.app `hsuby [`this])])) [])
                   (group
                    (tacticCalc_
                     "calc"
                     [(calcStep
                       («term_≤_»
                        (Term.app `edist [`z' `y'])
                        "≤"
                        (Init.Logic.«term_+_» (Term.app `edist [`z' `x]) "+" (Term.app `edist [`x `y'])))
                       ":="
                       (Term.app `edist_triangle [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Init.Logic.«term_+_»
                         (Init.Logic.«term_+_» (Term.app `edist [`z `z']) "+" (Term.app `edist [`z `x]))
                         "+"
                         (Init.Logic.«term_+_» (Term.app `edist [`y `x]) "+" (Term.app `edist [`y `y']))))
                       ":="
                       (Term.app
                        `add_le_add
                        [(Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                         (Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
                      (calcStep
                       («term_<_»
                        (Term.hole "_")
                        "<"
                        (Init.Logic.«term_+_»
                         (Init.Logic.«term_+_»
                          (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                          "+"
                          (Cardinal.SetTheory.Cardinal.«term_^_»
                           (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                           "^"
                           (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1"))))
                         "+"
                         (Init.Logic.«term_+_»
                          (Cardinal.SetTheory.Cardinal.«term_^_»
                           (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                           "^"
                           (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))
                          "+"
                          (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m))))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.applyRules "apply_rules" [] "[" [`Ennreal.add_lt_add] "]" []) [])]))))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Finset.Data.Finset.Fold.«term_*_»
                         (numLit "2")
                         "*"
                         (Init.Logic.«term_+_»
                          (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                          "+"
                          (Cardinal.SetTheory.Cardinal.«term_^_»
                           (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                           "^"
                           (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1"))))))
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
                             ["[" [(Tactic.simpLemma [] [] `two_mul) "," (Tactic.simpLemma [] [] `add_commₓ)] "]"]
                             [])
                            [])]))))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Finset.Data.Finset.Fold.«term_*_»
                         (numLit "2")
                         "*"
                         (Init.Logic.«term_+_»
                          (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                          "+"
                          (Cardinal.SetTheory.Cardinal.«term_^_»
                           (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                           "^"
                           (Init.Logic.«term_+_» `m "+" (numLit "1"))))))
                       ":="
                       («term_$__»
                        (Term.app `Ennreal.mul_le_mul [`le_rfl])
                        "$"
                        («term_$__»
                         (Term.app `add_le_add [`le_rfl])
                         "$"
                         (Term.app `hpow_le [(Term.app `add_le_add [`hm `le_rfl])]))))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Finset.Data.Finset.Fold.«term_*_»
                         (numLit "3")
                         "*"
                         (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)))
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
                              [(Tactic.rwRule [] `mul_addₓ)
                               ","
                               (Tactic.rwRule [] `h2pow)
                               ","
                               (Tactic.rwRule [] `bit1)
                               ","
                               (Tactic.rwRule [] `add_mulₓ)
                               ","
                               (Tactic.rwRule [] `one_mulₓ)]
                              "]")
                             [])
                            [])]))))])
                    [])]))))))
            [])
           (group
            (Tactic.have''
             "have"
             []
             [(Term.typeSpec
               ":"
               (Term.proj
                (Set.Data.Set.Lattice.«term⋃_,_»
                 "⋃"
                 (Lean.explicitBinders
                  [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `m)] ":" (Term.hole "_") ")")
                   (Lean.bracketedExplicitBinders
                    "("
                    [(Lean.binderIdent "_")]
                    ":"
                    («term_≤_» `m "≤" (Init.Logic.«term_+_» `n "+" `k))
                    ")")
                   (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
                   (Lean.bracketedExplicitBinders
                    "("
                    [(Lean.binderIdent "_")]
                    ":"
                    (Init.Core.«term_∈_»
                     `i
                     " ∈ "
                     (Set.«term{_|_}»
                      "{"
                      (Mathlib.ExtendedBinder.extBinder `i [":" `ι])
                      "|"
                      (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `i]) " ∩ " `B) "." `Nonempty)
                      "}"))
                    ")")])
                 ", "
                 (Set.«term{_}» "{" [(Term.paren "(" [`m [(Term.tupleTail "," [`i])]] ")")] "}"))
                "."
                `Finite))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj (Term.app `finite_le_nat [(Term.hole "_")]) "." `bUnion)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i `hi] [])]
                 "=>"
                 (Term.app
                  (Term.proj (Term.proj (Term.app `Hle [`i `hi]) "." `Finite) "." `bUnion)
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                     "=>"
                     (Term.app `finite_singleton [(Term.hole "_")])))])))]))
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `this.subset
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`I `hI] [])] "=>" (Term.hole "_")))]))
            [])
           (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_Union)] "]"] []) [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.proj `I "." (fieldIdx "1"))
               ","
               (Term.hole "_")
               ","
               (Term.proj `I "." (fieldIdx "2"))
               ","
               `hI
               ","
               `prod.mk.eta.symm]
              "⟩"))
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj `not_ltₓ "." (fieldIdx "1"))
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`hlt] [])]
                 "=>"
                 (Term.app
                  `Hgt
                  [(Term.proj `I "." (fieldIdx "1")) `hlt (Term.proj `I "." (fieldIdx "2")) `hI.some_spec])))]))
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
     [(group (Tactic.intro "intro" [`x]) [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `Dcov [`x]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hn)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.have''
        "have"
        []
        [(Term.typeSpec
          ":"
          (Init.Core.«term_∈_» (Term.app `D [`n `i]) " ∈ " (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])))])
       [])
      (group
       (Tactic.exact "exact" (Term.app `IsOpen.mem_nhds [(Term.app `Dopen [(Term.hole "_") (Term.hole "_")]) `hn]))
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget
          []
          (Term.app
           (Term.proj
            (Term.proj (Term.app `nhds_basis_uniformity [`uniformity_basis_edist_inv_two_pow]) "." `mem_iff)
            "."
            (fieldIdx "1"))
           [`this]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
           ","
           (Tactic.rcasesPatLo
            (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hsub)])
            [":"
             (Init.Core.«term_⊆_»
              (Term.app
               `ball
               [`x (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k)])
              " ⊆ "
              (Term.app `D [`n `i]))])]
          "⟩")])
       [])
      (group
       (Tactic.set
        "set"
        `B
        []
        ":="
        (Term.app
         `ball
         [`x
          (Cardinal.SetTheory.Cardinal.«term_^_»
           (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
           "^"
           (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))])
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`B "," (Term.app `ball_mem_nhds [(Term.hole "_") (Term.app `pow_pos [(Term.hole "_")])]) "," (Term.hole "_")]
         "⟩"))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`Hgt []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `m
              (Mathlib.ExtendedBinder.«binderTerm≥_»
               "≥"
               (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))
              ","
              (Term.forall
               "∀"
               [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
               ","
               (Term.app `Disjoint [(Term.app `D [`m `i]) `B])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `hm))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `i))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `y))
                 (Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hym)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyx)]) [])]
                   "⟩"))]
                [])
               [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hym]))]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzi)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `H)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hz)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.have''
                "have"
                []
                [(Term.typeSpec
                  ":"
                  (Init.Core.«term_∉_»
                   `z
                   " ∉ "
                   (Term.app
                    `ball
                    [`x (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k)])))])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`hz] [])]
                  "=>"
                  (Term.app
                   `H
                   [`n
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))
                    `i
                    (Term.app `hsub [`hz])]))))
               [])
              (group (Tactic.apply "apply" `this) [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_≤_»
                   (Term.app `edist [`z `x])
                   "≤"
                   (Init.Logic.«term_+_» (Term.app `edist [`y `z]) "+" (Term.app `edist [`y `x])))
                  ":="
                  (Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_<_»
                   (Term.hole "_")
                   "<"
                   (Init.Logic.«term_+_»
                    (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                    "+"
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                     "^"
                     (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))))
                  ":="
                  (Term.app `Ennreal.add_lt_add [`hz `hyx]))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Init.Logic.«term_+_»
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                     "^"
                     (Init.Logic.«term_+_» `k "+" (numLit "1")))
                    "+"
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                     "^"
                     (Init.Logic.«term_+_» `k "+" (numLit "1")))))
                  ":="
                  (Term.app
                   `add_le_add
                   [(«term_$__»
                     `hpow_le
                     "$"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))
                    («term_$__»
                     `hpow_le
                     "$"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `k))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `two_mul) "," (Tactic.rwRule [] `h2pow)] "]")
                        [])
                       [])]))))])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`Hle []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `m
              (Mathlib.ExtendedBinder.«binderTerm≤_» "≤" (Init.Logic.«term_+_» `n "+" `k))
              ","
              (Term.forall
               "∀"
               []
               ","
               (Term.app
                `Set.Subsingleton
                [(Set.«term{_|_}»
                  "{"
                  `j
                  "|"
                  (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `j]) " ∩ " `B) "." `Nonempty)
                  "}")])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `hm))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `j₁))
                 (Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyD)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hyB)]) [])]
                   "⟩"))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `j₂))
                 (Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzD)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hzB)]) [])]
                   "⟩"))]
                [])
               [])
              (group (byContra "by_contra" [`h]) [])
              (group
               (Tactic.wlog
                "wlog"
                []
                [`h]
                [":" («term_<_» `j₁ "<" `j₂)]
                [":=" (Term.app `Ne.lt_or_lt [`h])]
                ["using" [[`j₁ `j₂ `y `z] "," [`j₂ `j₁ `z `y]]])
               [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hyD]))]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `y')]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hsuby)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdisty)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app (Term.proj `memD "." (fieldIdx "1")) [`hzD]))]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `z')]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hdistz)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.suffices'
                "suffices"
                []
                [(Term.typeSpec
                  ":"
                  («term_<_»
                   (Term.app `edist [`z' `y'])
                   "<"
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "3")
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m))))])
               [])
              (group (Tactic.exact "exact" (Term.app `nmem_of_lt_ind [`h (Term.app `hsuby [`this])])) [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_≤_»
                   (Term.app `edist [`z' `y'])
                   "≤"
                   (Init.Logic.«term_+_» (Term.app `edist [`z' `x]) "+" (Term.app `edist [`x `y'])))
                  ":="
                  (Term.app `edist_triangle [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Init.Logic.«term_+_»
                    (Init.Logic.«term_+_» (Term.app `edist [`z `z']) "+" (Term.app `edist [`z `x]))
                    "+"
                    (Init.Logic.«term_+_» (Term.app `edist [`y `x]) "+" (Term.app `edist [`y `y']))))
                  ":="
                  (Term.app
                   `add_le_add
                   [(Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                    (Term.app `edist_triangle_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))
                 (calcStep
                  («term_<_»
                   (Term.hole "_")
                   "<"
                   (Init.Logic.«term_+_»
                    (Init.Logic.«term_+_»
                     (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                     "+"
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                      "^"
                      (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1"))))
                    "+"
                    (Init.Logic.«term_+_»
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                      "^"
                      (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1")))
                     "+"
                     (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m))))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.applyRules "apply_rules" [] "[" [`Ennreal.add_lt_add] "]" []) [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "2")
                    "*"
                    (Init.Logic.«term_+_»
                     (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                     "+"
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                      "^"
                      (Init.Logic.«term_+_» (Init.Logic.«term_+_» `n "+" `k) "+" (numLit "1"))))))
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
                        ["[" [(Tactic.simpLemma [] [] `two_mul) "," (Tactic.simpLemma [] [] `add_commₓ)] "]"]
                        [])
                       [])]))))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "2")
                    "*"
                    (Init.Logic.«term_+_»
                     (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)
                     "+"
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹")
                      "^"
                      (Init.Logic.«term_+_» `m "+" (numLit "1"))))))
                  ":="
                  («term_$__»
                   (Term.app `Ennreal.mul_le_mul [`le_rfl])
                   "$"
                   («term_$__»
                    (Term.app `add_le_add [`le_rfl])
                    "$"
                    (Term.app `hpow_le [(Term.app `add_le_add [`hm `le_rfl])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "3")
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_» (Init.Logic.«term_⁻¹» (numLit "2") "⁻¹") "^" `m)))
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
                         [(Tactic.rwRule [] `mul_addₓ)
                          ","
                          (Tactic.rwRule [] `h2pow)
                          ","
                          (Tactic.rwRule [] `bit1)
                          ","
                          (Tactic.rwRule [] `add_mulₓ)
                          ","
                          (Tactic.rwRule [] `one_mulₓ)]
                         "]")
                        [])
                       [])]))))])
               [])]))))))
       [])
      (group
       (Tactic.have''
        "have"
        []
        [(Term.typeSpec
          ":"
          (Term.proj
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `m)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders
               "("
               [(Lean.binderIdent "_")]
               ":"
               («term_≤_» `m "≤" (Init.Logic.«term_+_» `n "+" `k))
               ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
              (Lean.bracketedExplicitBinders
               "("
               [(Lean.binderIdent "_")]
               ":"
               (Init.Core.«term_∈_»
                `i
                " ∈ "
                (Set.«term{_|_}»
                 "{"
                 (Mathlib.ExtendedBinder.extBinder `i [":" `ι])
                 "|"
                 (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `i]) " ∩ " `B) "." `Nonempty)
                 "}"))
               ")")])
            ", "
            (Set.«term{_}» "{" [(Term.paren "(" [`m [(Term.tupleTail "," [`i])]] ")")] "}"))
           "."
           `Finite))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj (Term.app `finite_le_nat [(Term.hole "_")]) "." `bUnion)
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i `hi] [])]
            "=>"
            (Term.app
             (Term.proj (Term.proj (Term.app `Hle [`i `hi]) "." `Finite) "." `bUnion)
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                "=>"
                (Term.app `finite_singleton [(Term.hole "_")])))])))]))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `this.subset
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`I `hI] [])] "=>" (Term.hole "_")))]))
       [])
      (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_Union)] "]"] []) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.proj `I "." (fieldIdx "1"))
          ","
          (Term.hole "_")
          ","
          (Term.proj `I "." (fieldIdx "2"))
          ","
          `hI
          ","
          `prod.mk.eta.symm]
         "⟩"))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj `not_ltₓ "." (fieldIdx "1"))
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`hlt] [])]
            "=>"
            (Term.app
             `Hgt
             [(Term.proj `I "." (fieldIdx "1")) `hlt (Term.proj `I "." (fieldIdx "2")) `hI.some_spec])))]))
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
    (Term.proj `not_ltₓ "." (fieldIdx "1"))
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`hlt] [])]
       "=>"
       (Term.app `Hgt [(Term.proj `I "." (fieldIdx "1")) `hlt (Term.proj `I "." (fieldIdx "2")) `hI.some_spec])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `not_ltₓ "." (fieldIdx "1"))
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`hlt] [])]
      "=>"
      (Term.app `Hgt [(Term.proj `I "." (fieldIdx "1")) `hlt (Term.proj `I "." (fieldIdx "2")) `hI.some_spec])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`hlt] [])]
    "=>"
    (Term.app `Hgt [(Term.proj `I "." (fieldIdx "1")) `hlt (Term.proj `I "." (fieldIdx "2")) `hI.some_spec])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Hgt [(Term.proj `I "." (fieldIdx "1")) `hlt (Term.proj `I "." (fieldIdx "2")) `hI.some_spec])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hI.some_spec
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `I "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hlt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `I "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Hgt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `not_ltₓ "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `not_ltₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Term.proj `I "." (fieldIdx "1"))
     ","
     (Term.hole "_")
     ","
     (Term.proj `I "." (fieldIdx "2"))
     ","
     `hI
     ","
     `prod.mk.eta.symm]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.proj `I "." (fieldIdx "1"))
    ","
    (Term.hole "_")
    ","
    (Term.proj `I "." (fieldIdx "2"))
    ","
    `hI
    ","
    `prod.mk.eta.symm]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `prod.mk.eta.symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hI
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `I "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `I "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_Union)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app `this.subset [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`I `hI] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `this.subset [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`I `hI] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`I `hI] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this.subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.proj (Term.app `finite_le_nat [(Term.hole "_")]) "." `bUnion)
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i `hi] [])]
       "=>"
       (Term.app
        (Term.proj (Term.proj (Term.app `Hle [`i `hi]) "." `Finite) "." `bUnion)
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
           "=>"
           (Term.app `finite_singleton [(Term.hole "_")])))])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `finite_le_nat [(Term.hole "_")]) "." `bUnion)
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i `hi] [])]
      "=>"
      (Term.app
       (Term.proj (Term.proj (Term.app `Hle [`i `hi]) "." `Finite) "." `bUnion)
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
          "=>"
          (Term.app `finite_singleton [(Term.hole "_")])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i `hi] [])]
    "=>"
    (Term.app
     (Term.proj (Term.proj (Term.app `Hle [`i `hi]) "." `Finite) "." `bUnion)
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
        "=>"
        (Term.app `finite_singleton [(Term.hole "_")])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.proj (Term.app `Hle [`i `hi]) "." `Finite) "." `bUnion)
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
      "=>"
      (Term.app `finite_singleton [(Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
    "=>"
    (Term.app `finite_singleton [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finite_singleton [(Term.hole "_")])
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
  `finite_singleton
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj (Term.app `Hle [`i `hi]) "." `Finite) "." `bUnion)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `Hle [`i `hi]) "." `Finite)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Hle [`i `hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Hle
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Hle [`i `hi]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `finite_le_nat [(Term.hole "_")]) "." `bUnion)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `finite_le_nat [(Term.hole "_")])
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
  `finite_le_nat
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `finite_le_nat [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.have''
   "have"
   []
   [(Term.typeSpec
     ":"
     (Term.proj
      (Set.Data.Set.Lattice.«term⋃_,_»
       "⋃"
       (Lean.explicitBinders
        [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `m)] ":" (Term.hole "_") ")")
         (Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent "_")]
          ":"
          («term_≤_» `m "≤" (Init.Logic.«term_+_» `n "+" `k))
          ")")
         (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
         (Lean.bracketedExplicitBinders
          "("
          [(Lean.binderIdent "_")]
          ":"
          (Init.Core.«term_∈_»
           `i
           " ∈ "
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder `i [":" `ι])
            "|"
            (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `i]) " ∩ " `B) "." `Nonempty)
            "}"))
          ")")])
       ", "
       (Set.«term{_}» "{" [(Term.paren "(" [`m [(Term.tupleTail "," [`i])]] ")")] "}"))
      "."
      `Finite))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.have''', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `m)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent "_")]
       ":"
       («term_≤_» `m "≤" (Init.Logic.«term_+_» `n "+" `k))
       ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent "_")]
       ":"
       (Init.Core.«term_∈_»
        `i
        " ∈ "
        (Set.«term{_|_}»
         "{"
         (Mathlib.ExtendedBinder.extBinder `i [":" `ι])
         "|"
         (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `i]) " ∩ " `B) "." `Nonempty)
         "}"))
       ")")])
    ", "
    (Set.«term{_}» "{" [(Term.paren "(" [`m [(Term.tupleTail "," [`i])]] ")")] "}"))
   "."
   `Finite)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `m)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent "_")]
      ":"
      («term_≤_» `m "≤" (Init.Logic.«term_+_» `n "+" `k))
      ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent "_")]
      ":"
      (Init.Core.«term_∈_»
       `i
       " ∈ "
       (Set.«term{_|_}»
        "{"
        (Mathlib.ExtendedBinder.extBinder `i [":" `ι])
        "|"
        (Term.proj (Init.Core.«term_∩_» (Term.app `D [`m `i]) " ∩ " `B) "." `Nonempty)
        "}"))
      ")")])
   ", "
   (Set.«term{_}» "{" [(Term.paren "(" [`m [(Term.tupleTail "," [`i])]] ")")] "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_}» "{" [(Term.paren "(" [`m [(Term.tupleTail "," [`i])]] ")")] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`m [(Term.tupleTail "," [`i])]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tupleTail', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A `pseudo_emetric_space` is always a paracompact space. Formalization is based
    on [MR0236876]. -/
  instance
    ( priority := 100 )
    [ PseudoEmetricSpace α ] : ParacompactSpace α
    :=
      by
        classical
          have pow_pos : ∀ k : ℕ , ( 0 : ℝ≥0∞ ) < 2 ⁻¹ ^ k
          exact fun k => Ennreal.pow_pos Ennreal.inv_pos . 2 Ennreal.two_ne_top _
          have hpow_le : ∀ { m n : ℕ } , m ≤ n → ( 2 ⁻¹ : ℝ≥0∞ ) ^ n ≤ 2 ⁻¹ ^ m
          exact fun m n h => Ennreal.pow_le_pow_of_le_one Ennreal.inv_le_one . 2 ennreal.one_lt_two.le h
          have
            h2pow
              : ∀ n : ℕ , 2 * ( 2 ⁻¹ : ℝ≥0∞ ) ^ n + 1 = 2 ⁻¹ ^ n
              :=
              by · intro n simp [ pow_succₓ , ← mul_assocₓ , Ennreal.mul_inv_cancel ]
          refine' ⟨ fun ι s ho hcov => _ ⟩
          simp only [ Union_eq_univ_iff ] at hcov
          let this' : LinearOrderₓ ι := linearOrderOfSTO' WellOrderingRel
          have wf : WellFounded ( · < · : ι → ι → Prop ) := @ IsWellOrder.wf ι WellOrderingRel _
          set ind : α → ι := fun x => wf.min { i : ι | x ∈ s i } hcov x
          have mem_ind : ∀ x , x ∈ s ind x
          exact fun x => wf.min_mem _ hcov x
          have nmem_of_lt_ind : ∀ { x i } , i < ind x → x ∉ s i
          exact fun x i hlt hxi => wf.not_lt_min _ hcov x hxi hlt
          set
            D
            : ℕ → ι → Set α
            :=
            fun
              n
                =>
                Nat.strongRecOn'
                  n
                    fun
                      n D' i
                        =>
                        ⋃
                          ( x : α )
                            ( hxs : ind x = i )
                            ( hb : ball x 3 * 2 ⁻¹ ^ n ⊆ s i )
                            ( hlt : ∀ , ∀ m < n , ∀ j : ι , x ∉ D' m ‹ _ › j )
                          ,
                          ball x 2 ⁻¹ ^ n
          have
            Dn
            :
              ∀
                n i
                ,
                D n i
                  =
                  ⋃
                    ( x : α )
                      ( hxs : ind x = i )
                      ( hb : ball x 3 * 2 ⁻¹ ^ n ⊆ s i )
                      ( hlt : ∀ , ∀ m < n , ∀ j : ι , x ∉ D m j )
                    ,
                    ball x 2 ⁻¹ ^ n
          exact fun n s => by simp only [ D ] rw [ Nat.strong_rec_on_beta' ]
          have
            memD
              :
                ∀
                  { n i y }
                  ,
                  y ∈ D n i
                    ↔
                    ∃
                      ( x : _ )
                        ( hi : ind x = i )
                        ( hb : ball x 3 * 2 ⁻¹ ^ n ⊆ s i )
                        ( hlt : ∀ , ∀ m < n , ∀ j : ι , x ∉ D m j )
                      ,
                      edist y x < 2 ⁻¹ ^ n
              :=
              by intro n i y rw [ Dn n i ] simp only [ mem_Union , mem_ball ]
          have
            Dcov
              : ∀ x , ∃ n i , x ∈ D n i
              :=
              by
                intro x
                  obtain ⟨ n , hn ⟩ : ∃ n : ℕ , ball x 3 * 2 ⁻¹ ^ n ⊆ s ind x
                  ·
                    rcases is_open_iff . 1 ho $ ind x x mem_ind x with ⟨ ε , ε0 , hε ⟩
                      have : 0 < ε / 3 := Ennreal.div_pos_iff . 2 ⟨ ε0.lt.ne' , Ennreal.coe_ne_top ⟩
                      rcases Ennreal.exists_inv_two_pow_lt this.ne' with ⟨ n , hn ⟩
                      refine' ⟨ n , subset.trans ball_subset_ball _ hε ⟩
                      simpa only [ div_eq_mul_inv , mul_commₓ ] using Ennreal.mul_lt_of_lt_div hn . le
                  by_contra h
                  push_neg at h
                  apply h n ind x
                  exact memD . 2 ⟨ x , rfl , hn , fun _ _ _ => h _ _ , mem_ball_self pow_pos _ ⟩
          have
            Dopen
              : ∀ n i , IsOpen D n i
              :=
              by intro n i rw [ Dn ] iterate 4 refine' is_open_Union fun _ => _ exact is_open_ball
          have
            HDS
              : ∀ n i , D n i ⊆ s i
              :=
              by
                intro n s x
                  rw [ memD ]
                  rintro ⟨ y , rfl , hsub , - , hyx ⟩
                  refine' hsub lt_of_lt_of_leₓ hyx _
                  calc 2 ⁻¹ ^ n = 1 * 2 ⁻¹ ^ n := one_mulₓ _ . symm _ ≤ 3 * 2 ⁻¹ ^ n := Ennreal.mul_le_mul _ le_rfl
                  have : ( ( 1 : ℕ ) : ℝ≥0∞ ) ≤ ( 3 : ℕ )
                  exact Ennreal.coe_nat_le_coe_nat . 2 by norm_num1
                  exact_mod_cast this
          refine' ⟨ ℕ × ι , fun ni => D ni . 1 ni . 2 , fun _ => Dopen _ _ , _ , _ , fun ni => ⟨ ni . 2 , HDS _ _ ⟩ ⟩
          · refine' Union_eq_univ_iff . 2 fun x => _ rcases Dcov x with ⟨ n , i , h ⟩ exact ⟨ ⟨ n , i ⟩ , h ⟩
          ·
            intro x
              rcases Dcov x with ⟨ n , i , hn ⟩
              have : D n i ∈ 𝓝 x
              exact IsOpen.mem_nhds Dopen _ _ hn
              rcases
                nhds_basis_uniformity uniformity_basis_edist_inv_two_pow . mem_iff . 1 this
                with ⟨ k , - , hsub : ball x 2 ⁻¹ ^ k ⊆ D n i ⟩
              set B := ball x 2 ⁻¹ ^ n + k + 1
              refine' ⟨ B , ball_mem_nhds _ pow_pos _ , _ ⟩
              have
                Hgt
                  : ∀ , ∀ m ≥ n + k + 1 , ∀ i : ι , Disjoint D m i B
                  :=
                  by
                    rintro m hm i y ⟨ hym , hyx ⟩
                      rcases memD . 1 hym with ⟨ z , rfl , hzi , H , hz ⟩
                      have : z ∉ ball x 2 ⁻¹ ^ k
                      exact fun hz => H n by linarith i hsub hz
                      apply this
                      calc
                        edist z x ≤ edist y z + edist y x := edist_triangle_left _ _ _
                          _ < 2 ⁻¹ ^ m + 2 ⁻¹ ^ n + k + 1 := Ennreal.add_lt_add hz hyx
                          _ ≤ 2 ⁻¹ ^ k + 1 + 2 ⁻¹ ^ k + 1 := add_le_add hpow_le $ by linarith hpow_le $ by linarith
                          _ = 2 ⁻¹ ^ k := by rw [ ← two_mul , h2pow ]
              have
                Hle
                  : ∀ , ∀ m ≤ n + k , ∀ , Set.Subsingleton { j | D m j ∩ B . Nonempty }
                  :=
                  by
                    rintro m hm j₁ ⟨ y , hyD , hyB ⟩ j₂ ⟨ z , hzD , hzB ⟩
                      by_contra h
                      wlog h : j₁ < j₂ := Ne.lt_or_lt h using j₁ j₂ y z , j₂ j₁ z y
                      rcases memD . 1 hyD with ⟨ y' , rfl , hsuby , - , hdisty ⟩
                      rcases memD . 1 hzD with ⟨ z' , rfl , - , - , hdistz ⟩
                      suffices : edist z' y' < 3 * 2 ⁻¹ ^ m
                      exact nmem_of_lt_ind h hsuby this
                      calc
                        edist z' y' ≤ edist z' x + edist x y' := edist_triangle _ _ _
                          _ ≤ edist z z' + edist z x + edist y x + edist y y'
                            :=
                            add_le_add edist_triangle_left _ _ _ edist_triangle_left _ _ _
                          _ < 2 ⁻¹ ^ m + 2 ⁻¹ ^ n + k + 1 + 2 ⁻¹ ^ n + k + 1 + 2 ⁻¹ ^ m
                            :=
                            by apply_rules [ Ennreal.add_lt_add ]
                          _ = 2 * 2 ⁻¹ ^ m + 2 ⁻¹ ^ n + k + 1 := by simp only [ two_mul , add_commₓ ]
                          _ ≤ 2 * 2 ⁻¹ ^ m + 2 ⁻¹ ^ m + 1
                            :=
                            Ennreal.mul_le_mul le_rfl $ add_le_add le_rfl $ hpow_le add_le_add hm le_rfl
                          _ = 3 * 2 ⁻¹ ^ m := by rw [ mul_addₓ , h2pow , bit1 , add_mulₓ , one_mulₓ ]
              have
                :
                  ⋃ ( m : _ ) ( _ : m ≤ n + k ) ( i : _ ) ( _ : i ∈ { i : ι | D m i ∩ B . Nonempty } ) , { ( m , i ) }
                    .
                    Finite
              exact finite_le_nat _ . bUnion fun i hi => Hle i hi . Finite . bUnion fun _ _ => finite_singleton _
              refine' this.subset fun I hI => _
              simp only [ mem_Union ]
              refine' ⟨ I . 1 , _ , I . 2 , hI , prod.mk.eta.symm ⟩
              exact not_ltₓ . 1 fun hlt => Hgt I . 1 hlt I . 2 hI.some_spec

instance (priority := 100) normal_of_emetric [EmetricSpace α] : NormalSpace α :=
  normal_of_paracompact_t2

end Emetric

