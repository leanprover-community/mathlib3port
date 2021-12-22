import Mathbin.SetTheory.CardinalOrdinal

/-!
# Cofinality

This file contains the definition of cofinality of a ordinal number and regular cardinals

## Main Definitions

* `ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `cardinal.is_limit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `cardinal.is_strong_limit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.
* `cardinal.is_regular c` means that `c` is a regular cardinal: `ω ≤ c ∧ c.ord.cof = c`.
* `cardinal.is_inaccessible c` means that `c` is strongly inaccessible:
  `ω < c ∧ is_regular c ∧ is_strong_limit c`.

## Main Statements

* `ordinal.infinite_pigeonhole_card`: the infinite pigeonhole principle
* `cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ω`
* `cardinal.univ_inaccessible`: The type of ordinals in `Type u` form an inaccessible cardinal
  (in `Type v` with `v > u`). This shows (externally) that in `Type u` there are at least `u`
  inaccessible cardinals.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.

## Tags

cofinality, regular cardinals, limits cardinals, inaccessible cardinals,
infinite pigeonhole principle


-/


noncomputable section

open Function Cardinal Set

open_locale Classical Cardinal

universe u v w

variable {α : Type _} {r : α → α → Prop}

namespace Order

/--  Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) [IsRefl α r] : Cardinal :=
  @Cardinal.min { S : Set α // ∀ a, ∃ b ∈ S, r a b } ⟨⟨Set.Univ, fun a => ⟨a, ⟨⟩, refl _⟩⟩⟩ fun S => # S

theorem cof_le (r : α → α → Prop) [IsRefl α r] {S : Set α} (h : ∀ a, ∃ b ∈ S, r a b) : Order.cof r ≤ # S :=
  le_transₓ (Cardinal.min_le _ ⟨S, h⟩) (le_reflₓ _)

theorem le_cof {r : α → α → Prop} [IsRefl α r] (c : Cardinal) :
    c ≤ Order.cof r ↔ ∀ {S : Set α} h : ∀ a, ∃ b ∈ S, r a b, c ≤ # S := by
  rw [Order.cof, Cardinal.le_min]
  exact ⟨fun H S h => H ⟨S, h⟩, fun H ⟨S, h⟩ => H h⟩

end Order

theorem RelIso.Cof.aux {α : Type u} {β : Type v} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{max u v} (Order.cof r) ≤ Cardinal.lift.{max u v} (Order.cof s) := by
  rw [Order.cof, Order.cof, lift_min, lift_min, Cardinal.le_min]
  intro S
  cases' S with S H
  simp only [comp, coe_sort_coe_base, Subtype.coe_mk]
  refine' le_transₓ (min_le _ _) _
  ·
    exact
      ⟨f ⁻¹' S, fun a =>
        let ⟨b, bS, h⟩ := H (f a)
        ⟨f.symm b, by
          simp [bS, ← f.map_rel_iff, h, -coe_fn_coe_base, -coe_fn_coe_trans, PrincipalSeg.coe_coe_fn',
            InitialSeg.coe_coe_fn]⟩⟩
  ·
    exact
      lift_mk_le.{u, v, max u v}.2
        ⟨⟨fun ⟨x, h⟩ => ⟨f x, h⟩, fun ⟨x, h₁⟩ ⟨y, h₂⟩ h₃ => by
            congr <;> injection h₃ with h' <;> exact f.to_equiv.injective h'⟩⟩

theorem RelIso.cof {α : Type u} {β : Type v} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{max u v} (Order.cof r) = Cardinal.lift.{max u v} (Order.cof s) :=
  le_antisymmₓ (RelIso.Cof.aux f) (RelIso.Cof.aux f.symm)

def StrictOrder.cof (r : α → α → Prop) [h : IsIrrefl α r] : Cardinal :=
  @Order.cof α (fun x y => ¬r y x) ⟨h.1⟩

namespace Ordinal

/--  Cofinality of an ordinal. This is the smallest cardinal of a
  subset `S` of the ordinal which is unbounded, in the sense
  `∀ a, ∃ b ∈ S, ¬(b > a)`. It is defined for all ordinals, but
  `cof 0 = 0` and `cof (succ o) = 1`, so it is only really
  interesting on limit ordinals (when it is an infinite cardinal). -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  Quot.liftOn o
    (fun ⟨α, r, _⟩ => by
      exact StrictOrder.cof r)
    (by
      rintro ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨⟨f, hf⟩⟩
      rw [← Cardinal.lift_inj]
      apply RelIso.cof ⟨f, _⟩
      simp [hf])

theorem cof_type (r : α → α → Prop) [IsWellOrder α r] : (type r).cof = StrictOrder.cof r :=
  rfl

theorem le_cof_type [IsWellOrder α r] {c} : c ≤ cof (type r) ↔ ∀ S : Set α, (∀ a, ∃ b ∈ S, ¬r b a) → c ≤ # S := by
  dsimp [cof, StrictOrder.cof, Order.cof, type, Quotientₓ.mk, Quot.liftOn] <;>
    rw [Cardinal.le_min, Subtype.forall] <;> rfl

theorem cof_type_le [IsWellOrder α r] (S : Set α) (h : ∀ a, ∃ b ∈ S, ¬r b a) : cof (type r) ≤ # S :=
  le_cof_type.1 (le_reflₓ _) S h

theorem lt_cof_type [IsWellOrder α r] (S : Set α) (hl : # S < cof (type r)) : ∃ a, ∀, ∀ b ∈ S, ∀, r b a :=
  not_forall_not.1 $ fun h => not_le_of_lt hl $ cof_type_le S fun a => not_ball.1 (h a)

theorem cof_eq (r : α → α → Prop) [IsWellOrder α r] : ∃ S : Set α, (∀ a, ∃ b ∈ S, ¬r b a) ∧ # S = cof (type r) := by
  have : ∃ i, cof (type r) = _ := by
    dsimp [cof, Order.cof, type, Quotientₓ.mk, Quot.liftOn]
    apply Cardinal.min_eq
  exact
    let ⟨⟨S, hl⟩, e⟩ := this
    ⟨S, hl, e.symm⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `ord_cof_eq [])
  (Command.declSig
   [(Term.explicitBinder "(" [`r] [":" (Term.arrow `α "→" (Term.arrow `α "→" (Term.prop "Prop")))] [] ")")
    (Term.instBinder "[" [] (Term.app `IsWellOrder [`α `r]) "]")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `S)] [":" (Term.app `Set [`α])]))
     ","
     («term_∧_»
      (Term.forall
       "∀"
       [(Term.simpleBinder [`a] [])]
       ","
       (Mathlib.ExtendedBinder.«term∃___,_» "∃" `b («binderTerm∈_» "∈" `S) "," («term¬_» "¬" (Term.app `r [`b `a]))))
      "∧"
      («term_=_»
       (Term.app `type [(Term.app `Subrel [`r `S])])
       "="
       (Term.proj (Term.app `cof [(Term.app `type [`r])]) "." `ord))))))
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`S "," `hS "," `e] "⟩") [] [] ":=" (Term.app `cof_eq [`r])))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor "⟨" [`s "," (Term.hole "_") "," `e'] "⟩")
       []
       []
       ":="
       (Term.app `Cardinal.ord_eq [`S])))
     []
     (Term.let
      "let"
      (Term.letDecl
       (Term.letIdDecl
        `T
        []
        [(Term.typeSpec ":" (Term.app `Set [`α]))]
        ":="
        (Set.«term{_|_}»
         "{"
         `a
         "|"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders [(Lean.binderIdent `aS)] [":" (Init.Core.«term_∈_» `a " ∈ " `S)]))
          ","
          (Term.forall
           "∀"
           [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
           ","
           (Term.arrow
            (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")])
            "→"
            (Term.app `r [`b `a]))))
         "}")))
      []
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.skip "skip") [])
          (group (Tactic.suffices' "suffices" [] []) [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.anonymousCtor
                  "⟨"
                  [`T
                   ","
                   `this
                   ","
                   (Term.app
                    `le_antisymmₓ
                    [(Term.hole "_")
                     («term_$__»
                      (Term.proj `Cardinal.ord_le "." (fieldIdx "2"))
                      "$"
                      (Term.app `cof_type_le [`T `this]))])]
                  "⟩"))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e) "," (Tactic.rwRule [] `e')] "]")
                 [])
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  (Term.proj `type_le' "." (fieldIdx "2"))
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.app
                      `RelEmbedding.ofMonotone
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`a] [])]
                         "=>"
                         (Term.anonymousCtor
                          "⟨"
                          [`a
                           ","
                           (Term.let
                            "let"
                            (Term.letDecl
                             (Term.letPatDecl
                              (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
                              []
                              []
                              ":="
                              (Term.proj `a "." (fieldIdx "2"))))
                            []
                            `aS)]
                          "⟩")))
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
                    "⟩")]))
                [])
               (group
                (Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `a)]
                 ["with"
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `aS)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
                   "⟩")])
                [])
               (group
                (Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `b)]
                 ["with"
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb)]) [])]
                   "⟩")])
                [])
               (group
                (Tactic.change
                 "change"
                 (Term.app
                  `s
                  [(Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩")
                   (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")])
                 [])
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  (Term.proj
                   (Term.app
                    (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
                    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
                   "."
                   `resolve_left)
                  [(Term.hole "_")]))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.exact "exact" (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])])) [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intro "intro" [`e]) [])
                    (group (Tactic.injection "injection" `e ["with" [`e]]) [])
                    (group (Tactic.subst "subst" [`b]) [])
                    (group (Tactic.exact "exact" (Term.app `irrefl [(Term.hole "_") `h])) [])])))
                [])])))
           [])
          (group
           (Tactic.«tactic·._»
            "·"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`a]) [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     (Term.proj
                      (Set.«term{_|_}»
                       "{"
                       (Mathlib.ExtendedBinder.extBinder `b [":" `S])
                       "|"
                       («term¬_» "¬" (Term.app `r [`b `a]))
                       "}")
                      "."
                      `Nonempty))]
                   ":="
                   (Term.let
                    "let"
                    (Term.letDecl
                     (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩") [] [] ":=" (Term.app `hS [`a])))
                    []
                    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩")))))
                [])
               (group
                (Tactic.tacticLet_
                 "let"
                 (Term.letDecl
                  (Term.letIdDecl `b [] ":=" (Term.app (Term.proj `IsWellOrder.wf "." `min) [(Term.hole "_") `this]))))
                [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`ba []]
                   [(Term.typeSpec ":" («term¬_» "¬" (Term.app `r [`b `a])))]
                   ":="
                   (Term.app (Term.proj `IsWellOrder.wf "." `min_mem) [(Term.hole "_") `this]))))
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.anonymousCtor
                  "⟨"
                  [`b
                   ","
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.proj `b "." (fieldIdx "2"))
                     ","
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`c] [])]
                       "=>"
                       («term_$__»
                        (Term.proj `not_imp_not "." (fieldIdx "1"))
                        "$"
                        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
                    "⟩")
                   ","
                   `ba]
                  "⟩"))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    []
                    (Term.show
                     "show"
                     (Term.forall
                      "∀"
                      [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
                      ","
                      («term_=_»
                       (Term.paren
                        "("
                        [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩")
                         [(Term.typeAscription ":" `S)]]
                        ")")
                       "="
                       `b))
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.«tactic_<;>_»
                           (Tactic.intro "intro" [`b])
                           "<;>"
                           (Tactic.«tactic_<;>_»
                            (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                            "<;>"
                            (Tactic.tacticRfl "rfl")))
                          [])])))))]
                  "]")
                 [])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj `IsWellOrder.wf "." `not_lt_min)
                  [(Term.hole "_") `this (Term.app `IsOrderConnected.neg_trans [`h `ba])]))
                [])])))
           [])]))))))
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
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`S "," `hS "," `e] "⟩") [] [] ":=" (Term.app `cof_eq [`r])))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letPatDecl
      (Term.anonymousCtor "⟨" [`s "," (Term.hole "_") "," `e'] "⟩")
      []
      []
      ":="
      (Term.app `Cardinal.ord_eq [`S])))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letIdDecl
       `T
       []
       [(Term.typeSpec ":" (Term.app `Set [`α]))]
       ":="
       (Set.«term{_|_}»
        "{"
        `a
        "|"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `aS)] [":" (Init.Core.«term_∈_» `a " ∈ " `S)]))
         ","
         (Term.forall
          "∀"
          [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
          ","
          (Term.arrow
           (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")])
           "→"
           (Term.app `r [`b `a]))))
        "}")))
     []
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.skip "skip") [])
         (group (Tactic.suffices' "suffices" [] []) [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [`T
                  ","
                  `this
                  ","
                  (Term.app
                   `le_antisymmₓ
                   [(Term.hole "_")
                    («term_$__»
                     (Term.proj `Cardinal.ord_le "." (fieldIdx "2"))
                     "$"
                     (Term.app `cof_type_le [`T `this]))])]
                 "⟩"))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e) "," (Tactic.rwRule [] `e')] "]")
                [])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj `type_le' "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(Term.app
                     `RelEmbedding.ofMonotone
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`a] [])]
                        "=>"
                        (Term.anonymousCtor
                         "⟨"
                         [`a
                          ","
                          (Term.let
                           "let"
                           (Term.letDecl
                            (Term.letPatDecl
                             (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
                             []
                             []
                             ":="
                             (Term.proj `a "." (fieldIdx "2"))))
                           []
                           `aS)]
                         "⟩")))
                      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
                   "⟩")]))
               [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] `a)]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `aS)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] `b)]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.change
                "change"
                (Term.app
                 `s
                 [(Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩")
                  (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")])
                [])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj
                  (Term.app
                   (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
                   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
                  "."
                  `resolve_left)
                 [(Term.hole "_")]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.exact "exact" (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])])) [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`e]) [])
                   (group (Tactic.injection "injection" `e ["with" [`e]]) [])
                   (group (Tactic.subst "subst" [`b]) [])
                   (group (Tactic.exact "exact" (Term.app `irrefl [(Term.hole "_") `h])) [])])))
               [])])))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`a]) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.proj
                     (Set.«term{_|_}»
                      "{"
                      (Mathlib.ExtendedBinder.extBinder `b [":" `S])
                      "|"
                      («term¬_» "¬" (Term.app `r [`b `a]))
                      "}")
                     "."
                     `Nonempty))]
                  ":="
                  (Term.let
                   "let"
                   (Term.letDecl
                    (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩") [] [] ":=" (Term.app `hS [`a])))
                   []
                   (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩")))))
               [])
              (group
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl `b [] ":=" (Term.app (Term.proj `IsWellOrder.wf "." `min) [(Term.hole "_") `this]))))
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`ba []]
                  [(Term.typeSpec ":" («term¬_» "¬" (Term.app `r [`b `a])))]
                  ":="
                  (Term.app (Term.proj `IsWellOrder.wf "." `min_mem) [(Term.hole "_") `this]))))
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [`b
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.proj `b "." (fieldIdx "2"))
                    ","
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`c] [])]
                      "=>"
                      («term_$__»
                       (Term.proj `not_imp_not "." (fieldIdx "1"))
                       "$"
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
                   "⟩")
                  ","
                  `ba]
                 "⟩"))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.show
                    "show"
                    (Term.forall
                     "∀"
                     [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
                     ","
                     («term_=_»
                      (Term.paren
                       "("
                       [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩")
                        [(Term.typeAscription ":" `S)]]
                       ")")
                      "="
                      `b))
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.«tactic_<;>_»
                          (Tactic.intro "intro" [`b])
                          "<;>"
                          (Tactic.«tactic_<;>_»
                           (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                           "<;>"
                           (Tactic.tacticRfl "rfl")))
                         [])])))))]
                 "]")
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `IsWellOrder.wf "." `not_lt_min)
                 [(Term.hole "_") `this (Term.app `IsOrderConnected.neg_trans [`h `ba])]))
               [])])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Term.anonymousCtor "⟨" [`s "," (Term.hole "_") "," `e'] "⟩")
     []
     []
     ":="
     (Term.app `Cardinal.ord_eq [`S])))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letIdDecl
      `T
      []
      [(Term.typeSpec ":" (Term.app `Set [`α]))]
      ":="
      (Set.«term{_|_}»
       "{"
       `a
       "|"
       («term∃_,_»
        "∃"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders [(Lean.binderIdent `aS)] [":" (Init.Core.«term_∈_» `a " ∈ " `S)]))
        ","
        (Term.forall
         "∀"
         [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
         ","
         (Term.arrow
          (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")])
          "→"
          (Term.app `r [`b `a]))))
       "}")))
    []
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.skip "skip") [])
        (group (Tactic.suffices' "suffices" [] []) [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [`T
                 ","
                 `this
                 ","
                 (Term.app
                  `le_antisymmₓ
                  [(Term.hole "_")
                   («term_$__»
                    (Term.proj `Cardinal.ord_le "." (fieldIdx "2"))
                    "$"
                    (Term.app `cof_type_le [`T `this]))])]
                "⟩"))
              [])
             (group
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e) "," (Tactic.rwRule [] `e')] "]") [])
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj `type_le' "." (fieldIdx "2"))
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app
                    `RelEmbedding.ofMonotone
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`a] [])]
                       "=>"
                       (Term.anonymousCtor
                        "⟨"
                        [`a
                         ","
                         (Term.let
                          "let"
                          (Term.letDecl
                           (Term.letPatDecl
                            (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
                            []
                            []
                            ":="
                            (Term.proj `a "." (fieldIdx "2"))))
                          []
                          `aS)]
                        "⟩")))
                     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
                  "⟩")]))
              [])
             (group
              (Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `a)]
               ["with"
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `aS)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
                 "⟩")])
              [])
             (group
              (Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `b)]
               ["with"
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb)]) [])]
                 "⟩")])
              [])
             (group
              (Tactic.change
               "change"
               (Term.app
                `s
                [(Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩")
                 (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")])
               [])
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
                 "."
                 `resolve_left)
                [(Term.hole "_")]))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.exact "exact" (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])])) [])])))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Tactic.intro "intro" [`e]) [])
                  (group (Tactic.injection "injection" `e ["with" [`e]]) [])
                  (group (Tactic.subst "subst" [`b]) [])
                  (group (Tactic.exact "exact" (Term.app `irrefl [(Term.hole "_") `h])) [])])))
              [])])))
         [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.intro "intro" [`a]) [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   (Term.proj
                    (Set.«term{_|_}»
                     "{"
                     (Mathlib.ExtendedBinder.extBinder `b [":" `S])
                     "|"
                     («term¬_» "¬" (Term.app `r [`b `a]))
                     "}")
                    "."
                    `Nonempty))]
                 ":="
                 (Term.let
                  "let"
                  (Term.letDecl
                   (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩") [] [] ":=" (Term.app `hS [`a])))
                  []
                  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩")))))
              [])
             (group
              (Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letIdDecl `b [] ":=" (Term.app (Term.proj `IsWellOrder.wf "." `min) [(Term.hole "_") `this]))))
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`ba []]
                 [(Term.typeSpec ":" («term¬_» "¬" (Term.app `r [`b `a])))]
                 ":="
                 (Term.app (Term.proj `IsWellOrder.wf "." `min_mem) [(Term.hole "_") `this]))))
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [`b
                 ","
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.proj `b "." (fieldIdx "2"))
                   ","
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`c] [])]
                     "=>"
                     («term_$__»
                      (Term.proj `not_imp_not "." (fieldIdx "1"))
                      "$"
                      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
                  "⟩")
                 ","
                 `ba]
                "⟩"))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.show
                   "show"
                   (Term.forall
                    "∀"
                    [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
                    ","
                    («term_=_»
                     (Term.paren
                      "("
                      [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩")
                       [(Term.typeAscription ":" `S)]]
                      ")")
                     "="
                     `b))
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.«tactic_<;>_»
                         (Tactic.intro "intro" [`b])
                         "<;>"
                         (Tactic.«tactic_<;>_»
                          (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                          "<;>"
                          (Tactic.tacticRfl "rfl")))
                        [])])))))]
                "]")
               [])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.app
                (Term.proj `IsWellOrder.wf "." `not_lt_min)
                [(Term.hole "_") `this (Term.app `IsOrderConnected.neg_trans [`h `ba])]))
              [])])))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `T
     []
     [(Term.typeSpec ":" (Term.app `Set [`α]))]
     ":="
     (Set.«term{_|_}»
      "{"
      `a
      "|"
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `aS)] [":" (Init.Core.«term_∈_» `a " ∈ " `S)]))
       ","
       (Term.forall
        "∀"
        [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
        ","
        (Term.arrow
         (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")])
         "→"
         (Term.app `r [`b `a]))))
      "}")))
   []
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.skip "skip") [])
       (group (Tactic.suffices' "suffices" [] []) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`T
                ","
                `this
                ","
                (Term.app
                 `le_antisymmₓ
                 [(Term.hole "_")
                  («term_$__» (Term.proj `Cardinal.ord_le "." (fieldIdx "2")) "$" (Term.app `cof_type_le [`T `this]))])]
               "⟩"))
             [])
            (group
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e) "," (Tactic.rwRule [] `e')] "]") [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj `type_le' "." (fieldIdx "2"))
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.app
                   `RelEmbedding.ofMonotone
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`a] [])]
                      "=>"
                      (Term.anonymousCtor
                       "⟨"
                       [`a
                        ","
                        (Term.let
                         "let"
                         (Term.letDecl
                          (Term.letPatDecl
                           (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
                           []
                           []
                           ":="
                           (Term.proj `a "." (fieldIdx "2"))))
                         []
                         `aS)]
                       "⟩")))
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
                 "⟩")]))
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `a)]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `aS)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `b)]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.change
              "change"
              (Term.app
               `s
               [(Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩")
                (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")])
              [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
                "."
                `resolve_left)
               [(Term.hole "_")]))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.exact "exact" (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])])) [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`e]) [])
                 (group (Tactic.injection "injection" `e ["with" [`e]]) [])
                 (group (Tactic.subst "subst" [`b]) [])
                 (group (Tactic.exact "exact" (Term.app `irrefl [(Term.hole "_") `h])) [])])))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`a]) [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Term.proj
                   (Set.«term{_|_}»
                    "{"
                    (Mathlib.ExtendedBinder.extBinder `b [":" `S])
                    "|"
                    («term¬_» "¬" (Term.app `r [`b `a]))
                    "}")
                   "."
                   `Nonempty))]
                ":="
                (Term.let
                 "let"
                 (Term.letDecl
                  (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩") [] [] ":=" (Term.app `hS [`a])))
                 []
                 (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩")))))
             [])
            (group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl `b [] ":=" (Term.app (Term.proj `IsWellOrder.wf "." `min) [(Term.hole "_") `this]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`ba []]
                [(Term.typeSpec ":" («term¬_» "¬" (Term.app `r [`b `a])))]
                ":="
                (Term.app (Term.proj `IsWellOrder.wf "." `min_mem) [(Term.hole "_") `this]))))
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`b
                ","
                (Term.anonymousCtor
                 "⟨"
                 [(Term.proj `b "." (fieldIdx "2"))
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`c] [])]
                    "=>"
                    («term_$__»
                     (Term.proj `not_imp_not "." (fieldIdx "1"))
                     "$"
                     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
                 "⟩")
                ","
                `ba]
               "⟩"))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.show
                  "show"
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
                   ","
                   («term_=_»
                    (Term.paren
                     "("
                     [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩")
                      [(Term.typeAscription ":" `S)]]
                     ")")
                    "="
                    `b))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.«tactic_<;>_»
                        (Tactic.intro "intro" [`b])
                        "<;>"
                        (Tactic.«tactic_<;>_»
                         (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                         "<;>"
                         (Tactic.tacticRfl "rfl")))
                       [])])))))]
               "]")
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj `IsWellOrder.wf "." `not_lt_min)
               [(Term.hole "_") `this (Term.app `IsOrderConnected.neg_trans [`h `ba])]))
             [])])))
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.skip "skip") [])
      (group (Tactic.suffices' "suffices" [] []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`T
               ","
               `this
               ","
               (Term.app
                `le_antisymmₓ
                [(Term.hole "_")
                 («term_$__» (Term.proj `Cardinal.ord_le "." (fieldIdx "2")) "$" (Term.app `cof_type_le [`T `this]))])]
              "⟩"))
            [])
           (group
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e) "," (Tactic.rwRule [] `e')] "]") [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj `type_le' "." (fieldIdx "2"))
              [(Term.anonymousCtor
                "⟨"
                [(Term.app
                  `RelEmbedding.ofMonotone
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`a] [])]
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [`a
                       ","
                       (Term.let
                        "let"
                        (Term.letDecl
                         (Term.letPatDecl
                          (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
                          []
                          []
                          ":="
                          (Term.proj `a "." (fieldIdx "2"))))
                        []
                        `aS)]
                      "⟩")))
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
                "⟩")]))
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `a)]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `aS)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `b)]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.change
             "change"
             (Term.app
              `s
              [(Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩")
               (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")])
             [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
                [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
               "."
               `resolve_left)
              [(Term.hole "_")]))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.exact "exact" (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])])) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`e]) [])
                (group (Tactic.injection "injection" `e ["with" [`e]]) [])
                (group (Tactic.subst "subst" [`b]) [])
                (group (Tactic.exact "exact" (Term.app `irrefl [(Term.hole "_") `h])) [])])))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`a]) [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Term.proj
                  (Set.«term{_|_}»
                   "{"
                   (Mathlib.ExtendedBinder.extBinder `b [":" `S])
                   "|"
                   («term¬_» "¬" (Term.app `r [`b `a]))
                   "}")
                  "."
                  `Nonempty))]
               ":="
               (Term.let
                "let"
                (Term.letDecl
                 (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩") [] [] ":=" (Term.app `hS [`a])))
                []
                (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩")))))
            [])
           (group
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl `b [] ":=" (Term.app (Term.proj `IsWellOrder.wf "." `min) [(Term.hole "_") `this]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`ba []]
               [(Term.typeSpec ":" («term¬_» "¬" (Term.app `r [`b `a])))]
               ":="
               (Term.app (Term.proj `IsWellOrder.wf "." `min_mem) [(Term.hole "_") `this]))))
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`b
               ","
               (Term.anonymousCtor
                "⟨"
                [(Term.proj `b "." (fieldIdx "2"))
                 ","
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`c] [])]
                   "=>"
                   («term_$__»
                    (Term.proj `not_imp_not "." (fieldIdx "1"))
                    "$"
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
                "⟩")
               ","
               `ba]
              "⟩"))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.show
                 "show"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
                  ","
                  («term_=_»
                   (Term.paren
                    "("
                    [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩")
                     [(Term.typeAscription ":" `S)]]
                    ")")
                   "="
                   `b))
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.«tactic_<;>_»
                       (Tactic.intro "intro" [`b])
                       "<;>"
                       (Tactic.«tactic_<;>_»
                        (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                        "<;>"
                        (Tactic.tacticRfl "rfl")))
                      [])])))))]
              "]")
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj `IsWellOrder.wf "." `not_lt_min)
              [(Term.hole "_") `this (Term.app `IsOrderConnected.neg_trans [`h `ba])]))
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
     [(group (Tactic.intro "intro" [`a]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.proj
             (Set.«term{_|_}»
              "{"
              (Mathlib.ExtendedBinder.extBinder `b [":" `S])
              "|"
              («term¬_» "¬" (Term.app `r [`b `a]))
              "}")
             "."
             `Nonempty))]
          ":="
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩") [] [] ":=" (Term.app `hS [`a])))
           []
           (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩")))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl `b [] ":=" (Term.app (Term.proj `IsWellOrder.wf "." `min) [(Term.hole "_") `this]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`ba []]
          [(Term.typeSpec ":" («term¬_» "¬" (Term.app `r [`b `a])))]
          ":="
          (Term.app (Term.proj `IsWellOrder.wf "." `min_mem) [(Term.hole "_") `this]))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`b
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.proj `b "." (fieldIdx "2"))
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`c] [])]
              "=>"
              («term_$__»
               (Term.proj `not_imp_not "." (fieldIdx "1"))
               "$"
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
           "⟩")
          ","
          `ba]
         "⟩"))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.show
            "show"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
             ","
             («term_=_»
              (Term.paren
               "("
               [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩") [(Term.typeAscription ":" `S)]]
               ")")
              "="
              `b))
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.«tactic_<;>_»
                  (Tactic.intro "intro" [`b])
                  "<;>"
                  (Tactic.«tactic_<;>_»
                   (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
                   "<;>"
                   (Tactic.tacticRfl "rfl")))
                 [])])))))]
         "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj `IsWellOrder.wf "." `not_lt_min)
         [(Term.hole "_") `this (Term.app `IsOrderConnected.neg_trans [`h `ba])]))
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
    (Term.proj `IsWellOrder.wf "." `not_lt_min)
    [(Term.hole "_") `this (Term.app `IsOrderConnected.neg_trans [`h `ba])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `IsWellOrder.wf "." `not_lt_min)
   [(Term.hole "_") `this (Term.app `IsOrderConnected.neg_trans [`h `ba])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IsOrderConnected.neg_trans [`h `ba])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ba
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsOrderConnected.neg_trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `IsOrderConnected.neg_trans [`h `ba]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
  (Term.proj `IsWellOrder.wf "." `not_lt_min)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `IsWellOrder.wf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
      (Term.show
       "show"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
        ","
        («term_=_»
         (Term.paren
          "("
          [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩") [(Term.typeAscription ":" `S)]]
          ")")
         "="
         `b))
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.«tactic_<;>_»
             (Tactic.intro "intro" [`b])
             "<;>"
             (Tactic.«tactic_<;>_»
              (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
              "<;>"
              (Tactic.tacticRfl "rfl")))
            [])])))))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   (Term.forall
    "∀"
    [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
    ","
    («term_=_»
     (Term.paren
      "("
      [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩") [(Term.typeAscription ":" `S)]]
      ")")
     "="
     `b))
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.«tactic_<;>_»
         (Tactic.intro "intro" [`b])
         "<;>"
         (Tactic.«tactic_<;>_»
          (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
          "<;>"
          (Tactic.tacticRfl "rfl")))
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.show.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.intro "intro" [`b])
   "<;>"
   (Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] []) "<;>" (Tactic.tacticRfl "rfl")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] []) "<;>" (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `b)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.intro "intro" [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
   ","
   («term_=_»
    (Term.paren
     "("
     [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩") [(Term.typeAscription ":" `S)]]
     ")")
    "="
    `b))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.paren
    "("
    [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩") [(Term.typeAscription ":" `S)]]
    ")")
   "="
   `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren
   "("
   [(Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩") [(Term.typeAscription ":" `S)]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," (Term.proj `b "." (fieldIdx "2"))] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `b "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [`b
     ","
     (Term.anonymousCtor
      "⟨"
      [(Term.proj `b "." (fieldIdx "2"))
       ","
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`c] [])]
         "=>"
         («term_$__»
          (Term.proj `not_imp_not "." (fieldIdx "1"))
          "$"
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
      "⟩")
     ","
     `ba]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`b
    ","
    (Term.anonymousCtor
     "⟨"
     [(Term.proj `b "." (fieldIdx "2"))
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`c] [])]
        "=>"
        («term_$__»
         (Term.proj `not_imp_not "." (fieldIdx "1"))
         "$"
         (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
     "⟩")
    ","
    `ba]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ba
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.proj `b "." (fieldIdx "2"))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`c] [])]
      "=>"
      («term_$__»
       (Term.proj `not_imp_not "." (fieldIdx "1"))
       "$"
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`c] [])]
    "=>"
    («term_$__»
     (Term.proj `not_imp_not "." (fieldIdx "1"))
     "$"
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.proj `not_imp_not "." (fieldIdx "1"))
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`h] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj `not_imp_not "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `not_imp_not
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `b "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`ba []]
     [(Term.typeSpec ":" («term¬_» "¬" (Term.app `r [`b `a])))]
     ":="
     (Term.app (Term.proj `IsWellOrder.wf "." `min_mem) [(Term.hole "_") `this]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `IsWellOrder.wf "." `min_mem) [(Term.hole "_") `this])
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
  (Term.proj `IsWellOrder.wf "." `min_mem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `IsWellOrder.wf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term¬_» "¬" (Term.app `r [`b `a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term¬_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `r [`b `a])
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
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 40, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl (Term.letIdDecl `b [] ":=" (Term.app (Term.proj `IsWellOrder.wf "." `min) [(Term.hole "_") `this]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `IsWellOrder.wf "." `min) [(Term.hole "_") `this])
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
  (Term.proj `IsWellOrder.wf "." `min)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `IsWellOrder.wf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
       (Term.proj
        (Set.«term{_|_}»
         "{"
         (Mathlib.ExtendedBinder.extBinder `b [":" `S])
         "|"
         («term¬_» "¬" (Term.app `r [`b `a]))
         "}")
        "."
        `Nonempty))]
     ":="
     (Term.let
      "let"
      (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩") [] [] ":=" (Term.app `hS [`a])))
      []
      (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩") [] [] ":=" (Term.app `hS [`a])))
   []
   (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩") "," `ba] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ba
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," `bS] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bS
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `hS [`a])
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
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," `bS "," `ba] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ba
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bS
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Set.«term{_|_}» "{" (Mathlib.ExtendedBinder.extBinder `b [":" `S]) "|" («term¬_» "¬" (Term.app `r [`b `a])) "}")
   "."
   `Nonempty)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_|_}» "{" (Mathlib.ExtendedBinder.extBinder `b [":" `S]) "|" («term¬_» "¬" (Term.app `r [`b `a])) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term¬_» "¬" (Term.app `r [`b `a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term¬_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `r [`b `a])
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
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 40, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`T
          ","
          `this
          ","
          (Term.app
           `le_antisymmₓ
           [(Term.hole "_")
            («term_$__» (Term.proj `Cardinal.ord_le "." (fieldIdx "2")) "$" (Term.app `cof_type_le [`T `this]))])]
         "⟩"))
       [])
      (group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e) "," (Tactic.rwRule [] `e')] "]") [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj `type_le' "." (fieldIdx "2"))
         [(Term.anonymousCtor
           "⟨"
           [(Term.app
             `RelEmbedding.ofMonotone
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`a] [])]
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [`a
                  ","
                  (Term.let
                   "let"
                   (Term.letDecl
                    (Term.letPatDecl
                     (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
                     []
                     []
                     ":="
                     (Term.proj `a "." (fieldIdx "2"))))
                   []
                   `aS)]
                 "⟩")))
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
           "⟩")]))
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `a)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `aS)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `b)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.change
        "change"
        (Term.app
         `s
         [(Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩") (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")])
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          (Term.app
           (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
           [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
          "."
          `resolve_left)
         [(Term.hole "_")]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.exact "exact" (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`e]) [])
           (group (Tactic.injection "injection" `e ["with" [`e]]) [])
           (group (Tactic.subst "subst" [`b]) [])
           (group (Tactic.exact "exact" (Term.app `irrefl [(Term.hole "_") `h])) [])])))
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
     [(group (Tactic.intro "intro" [`e]) [])
      (group (Tactic.injection "injection" `e ["with" [`e]]) [])
      (group (Tactic.subst "subst" [`b]) [])
      (group (Tactic.exact "exact" (Term.app `irrefl [(Term.hole "_") `h])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `irrefl [(Term.hole "_") `h]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `irrefl [(Term.hole "_") `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
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
  `irrefl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.subst "subst" [`b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.injection "injection" `e ["with" [`e]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.injection', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.exact "exact" (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `asymm [`h (Term.app `ha [(Term.hole "_") `hn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ha [(Term.hole "_") `hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
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
  `ha
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `ha [(Term.hole "_") `hn]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `asymm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj
     (Term.app
      (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
     "."
     `resolve_left)
    [(Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
    "."
    `resolve_left)
   [(Term.hole "_")])
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
  (Term.proj
   (Term.app
    (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
   "."
   `resolve_left)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) "." `resolve_left)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `trichotomous_of
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.paren "(" [(Term.app `trichotomous_of [`s (Term.hole "_") (Term.hole "_")]) []] ")")
    "."
    `resolve_left)
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`hn] [])] "=>" (Term.hole "_")))])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.change
   "change"
   (Term.app
    `s
    [(Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩") (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")])
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.change', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `s
   [(Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩") (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.anonymousCtor "⟨" [`a "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] `b)]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hb)]) [])]
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
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] `a)]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `aS)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
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
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj `type_le' "." (fieldIdx "2"))
    [(Term.anonymousCtor
      "⟨"
      [(Term.app
        `RelEmbedding.ofMonotone
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`a] [])]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [`a
             ","
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
                []
                []
                ":="
                (Term.proj `a "." (fieldIdx "2"))))
              []
              `aS)]
            "⟩")))
         (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
      "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `type_le' "." (fieldIdx "2"))
   [(Term.anonymousCtor
     "⟨"
     [(Term.app
       `RelEmbedding.ofMonotone
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`a] [])]
          "=>"
          (Term.anonymousCtor
           "⟨"
           [`a
            ","
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
               []
               []
               ":="
               (Term.proj `a "." (fieldIdx "2"))))
             []
             `aS)]
           "⟩")))
        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
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
   [(Term.app
     `RelEmbedding.ofMonotone
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`a] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [`a
          ","
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
             []
             []
             ":="
             (Term.proj `a "." (fieldIdx "2"))))
           []
           `aS)]
         "⟩")))
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `RelEmbedding.ofMonotone
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`a] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [`a
        ","
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
           []
           []
           ":="
           (Term.proj `a "." (fieldIdx "2"))))
         []
         `aS)]
       "⟩")))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `b `h] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [`a
      ","
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
         []
         []
         ":="
         (Term.proj `a "." (fieldIdx "2"))))
       []
       `aS)]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`a
    ","
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
       []
       []
       ":="
       (Term.proj `a "." (fieldIdx "2"))))
     []
     `aS)]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
     []
     []
     ":="
     (Term.proj `a "." (fieldIdx "2"))))
   []
   `aS)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `aS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.proj `a "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `aS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [`a
      ","
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`aS "," (Term.hole "_")] "⟩")
         []
         []
         ":="
         (Term.proj `a "." (fieldIdx "2"))))
       []
       `aS)]
     "⟩")))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `RelEmbedding.ofMonotone
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `type_le' "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `type_le'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e) "," (Tactic.rwRule [] `e')] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [`T
     ","
     `this
     ","
     (Term.app
      `le_antisymmₓ
      [(Term.hole "_")
       («term_$__» (Term.proj `Cardinal.ord_le "." (fieldIdx "2")) "$" (Term.app `cof_type_le [`T `this]))])]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`T
    ","
    `this
    ","
    (Term.app
     `le_antisymmₓ
     [(Term.hole "_")
      («term_$__» (Term.proj `Cardinal.ord_le "." (fieldIdx "2")) "$" (Term.app `cof_type_le [`T `this]))])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `le_antisymmₓ
   [(Term.hole "_")
    («term_$__» (Term.proj `Cardinal.ord_le "." (fieldIdx "2")) "$" (Term.app `cof_type_le [`T `this]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» (Term.proj `Cardinal.ord_le "." (fieldIdx "2")) "$" (Term.app `cof_type_le [`T `this]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `cof_type_le [`T `this])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `T
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `cof_type_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj `Cardinal.ord_le "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Cardinal.ord_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__» (Term.proj `Cardinal.ord_le "." (fieldIdx "2")) "$" (Term.app `cof_type_le [`T `this])) []]
 ")")
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
  `le_antisymmₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `T
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.suffices' "suffices" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.suffices'', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.skip "skip")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Set.«term{_|_}»
   "{"
   `a
   "|"
   («term∃_,_»
    "∃"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `aS)] [":" (Init.Core.«term_∈_» `a " ∈ " `S)]))
    ","
    (Term.forall
     "∀"
     [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
     ","
     (Term.arrow (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")]) "→" (Term.app `r [`b `a]))))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `aS)] [":" (Init.Core.«term_∈_» `a " ∈ " `S)]))
   ","
   (Term.forall
    "∀"
    [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
    ","
    (Term.arrow (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")]) "→" (Term.app `r [`b `a]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`b] [(Term.typeSpec ":" `S)])]
   ","
   (Term.arrow (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")]) "→" (Term.app `r [`b `a])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")]) "→" (Term.app `r [`b `a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `r [`b `a])
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
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Term.app `s [`b (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," `aS] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `aS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» `a " ∈ " `S)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
theorem
  ord_cof_eq
  ( r : α → α → Prop ) [ IsWellOrder α r ] : ∃ S : Set α , ∀ a , ∃ b ∈ S , ¬ r b a ∧ type Subrel r S = cof type r . ord
  :=
    let
      ⟨ S , hS , e ⟩ := cof_eq r
      let
        ⟨ s , _ , e' ⟩ := Cardinal.ord_eq S
        let
          T : Set α := { a | ∃ aS : a ∈ S , ∀ b : S , s b ⟨ _ , aS ⟩ → r b a }
          by
            skip
              suffices
              ·
                refine' ⟨ T , this , le_antisymmₓ _ Cardinal.ord_le . 2 $ cof_type_le T this ⟩
                  rw [ ← e , e' ]
                  refine'
                    type_le' . 2 ⟨ RelEmbedding.ofMonotone fun a => ⟨ a , let ⟨ aS , _ ⟩ := a . 2 aS ⟩ fun a b h => _ ⟩
                  rcases a with ⟨ a , aS , ha ⟩
                  rcases b with ⟨ b , bS , hb ⟩
                  change s ⟨ a , _ ⟩ ⟨ b , _ ⟩
                  refine' trichotomous_of s _ _ . resolve_left fun hn => _ . resolve_left _
                  · exact asymm h ha _ hn
                  · intro e injection e with e subst b exact irrefl _ h
              ·
                intro a
                  have : { b : S | ¬ r b a } . Nonempty := let ⟨ b , bS , ba ⟩ := hS a ⟨ ⟨ b , bS ⟩ , ba ⟩
                  let b := IsWellOrder.wf . min _ this
                  have ba : ¬ r b a := IsWellOrder.wf . min_mem _ this
                  refine' ⟨ b , ⟨ b . 2 , fun c => not_imp_not . 1 $ fun h => _ ⟩ , ba ⟩
                  rw [ show ∀ b : S , ( ⟨ b , b . 2 ⟩ : S ) = b by intro b <;> cases b <;> rfl ]
                  exact IsWellOrder.wf . not_lt_min _ this IsOrderConnected.neg_trans h ba

theorem lift_cof o : (cof o).lift = cof o.lift :=
  induction_on o $ by
    intros α r _
    cases' lift_type r with _ e
    rw [e]
    apply le_antisymmₓ
    ·
      (
        refine' le_cof_type.2 fun S H => _)
      have : (# (Ulift.up ⁻¹' S)).lift ≤ # S :=
        ⟨⟨fun ⟨⟨x, h⟩⟩ => ⟨⟨x⟩, h⟩, fun ⟨⟨x, h₁⟩⟩ ⟨⟨y, h₂⟩⟩ e => by
            simp at e <;> congr <;> injection e⟩⟩
      refine' le_transₓ (Cardinal.lift_le.2 $ cof_type_le _ _) this
      exact fun a =>
        let ⟨⟨b⟩, bs, br⟩ := H ⟨a⟩
        ⟨b, bs, br⟩
    ·
      rcases cof_eq r with ⟨S, H, e'⟩
      have : # (Ulift.down ⁻¹' S) ≤ (# S).lift :=
        ⟨⟨fun ⟨⟨x⟩, h⟩ => ⟨⟨x, h⟩⟩, fun ⟨⟨x⟩, h₁⟩ ⟨⟨y⟩, h₂⟩ e => by
            simp at e <;> congr <;> injections⟩⟩
      rw [e'] at this
      (
        refine' le_transₓ (cof_type_le _ _) this)
      exact fun ⟨a⟩ =>
        let ⟨b, bs, br⟩ := H a
        ⟨⟨b⟩, bs, br⟩

theorem cof_le_card o : cof o ≤ card o :=
  induction_on o $ fun α r _ => by
    skip
    have : # (@Set.Univ α) = card (type r) := Quotientₓ.sound ⟨Equivₓ.Set.univ _⟩
    rw [← this]
    exact cof_type_le Set.Univ fun a => ⟨a, ⟨⟩, irrefl a⟩

theorem cof_ord_le (c : Cardinal) : cof c.ord ≤ c := by
  simpa using cof_le_card c.ord

@[simp]
theorem cof_zero : cof 0 = 0 :=
  le_antisymmₓ
    (by
      simpa using cof_le_card 0)
    (Cardinal.zero_le _)

@[simp]
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 :=
  ⟨induction_on o $ fun α r _ z => by
      exact
        let ⟨S, hl, e⟩ := cof_eq r
        type_eq_zero_iff_is_empty.2 $
          ⟨fun a =>
            let ⟨b, h, _⟩ := hl a
            (mk_eq_zero_iff.1 (e.trans z)).elim' ⟨_, h⟩⟩,
    fun e => by
    simp [e]⟩

@[simp]
theorem cof_succ o : cof (succ o) = 1 := by
  apply le_antisymmₓ
  ·
    refine' induction_on o fun α r _ => _
    change cof (type _) ≤ _
    rw [← (_ : # _ = 1)]
    apply cof_type_le
    ·
      refine' fun a => ⟨Sum.inr PUnit.unit, Set.mem_singleton _, _⟩
      rcases a with (a | ⟨⟨⟨⟩⟩⟩) <;> simp [EmptyRelation]
    ·
      rw [Cardinal.mk_fintype, Set.card_singleton]
      simp
  ·
    rw [← Cardinal.succ_zero, Cardinal.succ_le]
    simpa [lt_iff_le_and_ne, Cardinal.zero_le] using fun h => succ_ne_zero o (cof_eq_zero.1 (Eq.symm h))

@[simp]
theorem cof_eq_one_iff_is_succ {o} : cof.{u} o = 1 ↔ ∃ a, o = succ a :=
  ⟨induction_on o $ fun α r _ z => by
      skip
      rcases cof_eq r with ⟨S, hl, e⟩
      rw [z] at e
      cases'
        mk_ne_zero_iff.1
          (by
            rw [e] <;> exact one_ne_zero) with
        a
      refine'
        ⟨typein r a,
          Eq.symm $ Quotientₓ.sound ⟨RelIso.ofSurjective (RelEmbedding.ofMonotone _ fun x y => _) fun x => _⟩⟩
      ·
        apply Sum.rec <;> [exact Subtype.val, exact fun _ => a]
      ·
        rcases x with (x | ⟨⟨⟨⟩⟩⟩) <;> rcases y with (y | ⟨⟨⟨⟩⟩⟩) <;> simp [Subrel, Order.Preimage, EmptyRelation]
        exact x.2
      ·
        suffices r x a ∨ ∃ b : PUnit, ↑a = x by
          simpa
        rcases trichotomous_of r x a with (h | h | h)
        ·
          exact Or.inl h
        ·
          exact Or.inr ⟨PUnit.unit, h.symm⟩
        ·
          rcases hl x with ⟨a', aS, hn⟩
          rw [(_ : ↑a = a')] at h
          ·
            exact absurd h hn
          refine' congr_argₓ Subtype.val (_ : a = ⟨a', aS⟩)
          have := le_one_iff_subsingleton.1 (le_of_eqₓ e)
          apply Subsingleton.elimₓ,
    fun ⟨a, e⟩ => by
    simp [e]⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `cof_add [])
  (Command.declSig
   [(Term.explicitBinder "(" [`a `b] [":" `Ordinal] [] ")")]
   (Term.typeSpec
    ":"
    (Term.arrow
     («term_≠_» `b "≠" (numLit "0"))
     "→"
     («term_=_» (Term.app `cof [(Init.Logic.«term_+_» `a "+" `b)]) "=" (Term.app `cof [`b])))))
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.app `induction_on [`a])
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`α `r (Term.hole "_")] [])]
      "=>"
      («term_$__»
       (Term.app `induction_on [`b])
       "$"
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`β `s (Term.hole "_") `b0] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.skip "skip") [])
             (group
              (Tactic.change
               "change"
               («term_=_» (Term.app `cof [(Term.app `type [(Term.hole "_")])]) "=" (Term.hole "_"))
               [])
              [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.app
                `eq_of_forall_le_iff
                [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.hole "_")))]))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_cof_type) "," (Tactic.rwRule [] `le_cof_type)] "]")
               [])
              [])
             (group
              (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`H `S `hS]))
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
                     `le_transₓ
                     [(Term.app
                       `H
                       [(Set.«term{_|_}»
                         "{"
                         `a
                         "|"
                         (Term.app
                          `Sum.recOn
                          [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
                         "}")
                        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                       "⟩")]))
                   [])
                  (group
                   (Tactic.«tactic·._»
                    "·"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.cases'
                         "cases'"
                         [(Tactic.casesTarget [] `a)]
                         []
                         ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.cases'
                              "cases'"
                              [(Tactic.casesTarget
                                []
                                (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
                              []
                              ["with" [(Lean.binderIdent `b)]])
                             [])
                            (group
                             (Tactic.rcases
                              "rcases"
                              [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                              ["with"
                               (Tactic.rcasesPat.tuple
                                "⟨"
                                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                                 ","
                                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                                 ","
                                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
                                "⟩")])
                             [])
                            (group
                             (Tactic.exact
                              "exact"
                              (Term.anonymousCtor
                               "⟨"
                               [(Term.app `Sum.inr [`b'])
                                ","
                                `bs
                                ","
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                               "⟩"))
                             [])])))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.rcases
                              "rcases"
                              [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                              ["with"
                               (Tactic.rcasesPat.tuple
                                "⟨"
                                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                                 ","
                                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                                 ","
                                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                                "⟩")])
                             [])
                            (group
                             (Tactic.exact
                              "exact"
                              (Term.anonymousCtor
                               "⟨"
                               [(Term.app `Sum.inr [`b'])
                                ","
                                `bs
                                ","
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group
                                     (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])
                                     [])])))]
                               "⟩"))
                             [])])))
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
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder [`a] [])]
                           "=>"
                           (Term.match
                            "match"
                            []
                            [(Term.matchDiscr [] `a)]
                            []
                            "with"
                            (Term.matchAlts
                             [(Term.matchAlt
                               "|"
                               [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
                               "=>"
                               (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
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
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder [`a `b] [])]
                           "=>"
                           (Term.match
                            "match"
                            []
                            [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
                            []
                            "with"
                            (Term.matchAlts
                             [(Term.matchAlt
                               "|"
                               [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
                                ","
                                (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
                                ","
                                `h]
                               "=>"
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(group
                                    (Tactic.«tactic_<;>_»
                                     (Tactic.congr "congr" [] [])
                                     "<;>"
                                     (Tactic.injection "injection" `h []))
                                    [])]))))])))))
                        [])])))
                   [])])))
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
                     `le_transₓ
                     [(Term.app
                       `H
                       [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
                        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                       "⟩")]))
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
                          [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
                          ["with"
                           (Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo
                              (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')])
                              [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                            "⟩")])
                         "<;>"
                         (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
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
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                           "=>"
                           (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
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
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
                            (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
                            (Term.simpleBinder [`h] [])]
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group
                                (Tactic.«tactic_<;>_»
                                 (Tactic.injection "injection" `h ["with" [`h]])
                                 "<;>"
                                 (Tactic.«tactic_<;>_»
                                  (Tactic.congr "congr" [] [])
                                  "<;>"
                                  (Tactic.injection "injection" `h [])))
                                [])]))))))
                        [])])))
                   [])])))
              [])])))))))))
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
  («term_$__»
   (Term.app `induction_on [`a])
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`α `r (Term.hole "_")] [])]
     "=>"
     («term_$__»
      (Term.app `induction_on [`b])
      "$"
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`β `s (Term.hole "_") `b0] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.skip "skip") [])
            (group
             (Tactic.change
              "change"
              («term_=_» (Term.app `cof [(Term.app `type [(Term.hole "_")])]) "=" (Term.hole "_"))
              [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               `eq_of_forall_le_iff
               [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.hole "_")))]))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_cof_type) "," (Tactic.rwRule [] `le_cof_type)] "]")
              [])
             [])
            (group
             (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`H `S `hS]))
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
                    `le_transₓ
                    [(Term.app
                      `H
                      [(Set.«term{_|_}»
                        "{"
                        `a
                        "|"
                        (Term.app
                         `Sum.recOn
                         [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
                        "}")
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                      "⟩")]))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.cases'
                        "cases'"
                        [(Tactic.casesTarget [] `a)]
                        []
                        ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.cases'
                             "cases'"
                             [(Tactic.casesTarget
                               []
                               (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
                             []
                             ["with" [(Lean.binderIdent `b)]])
                            [])
                           (group
                            (Tactic.rcases
                             "rcases"
                             [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                             ["with"
                              (Tactic.rcasesPat.tuple
                               "⟨"
                               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                                ","
                                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                                ","
                                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
                               "⟩")])
                            [])
                           (group
                            (Tactic.exact
                             "exact"
                             (Term.anonymousCtor
                              "⟨"
                              [(Term.app `Sum.inr [`b'])
                               ","
                               `bs
                               ","
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                              "⟩"))
                            [])])))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.rcases
                             "rcases"
                             [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                             ["with"
                              (Tactic.rcasesPat.tuple
                               "⟨"
                               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                                ","
                                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                                ","
                                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                               "⟩")])
                            [])
                           (group
                            (Tactic.exact
                             "exact"
                             (Term.anonymousCtor
                              "⟨"
                              [(Term.app `Sum.inr [`b'])
                               ","
                               `bs
                               ","
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
                              "⟩"))
                            [])])))
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
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`a] [])]
                          "=>"
                          (Term.match
                           "match"
                           []
                           [(Term.matchDiscr [] `a)]
                           []
                           "with"
                           (Term.matchAlts
                            [(Term.matchAlt
                              "|"
                              [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
                              "=>"
                              (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
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
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`a `b] [])]
                          "=>"
                          (Term.match
                           "match"
                           []
                           [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
                           []
                           "with"
                           (Term.matchAlts
                            [(Term.matchAlt
                              "|"
                              [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
                               ","
                               (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
                               ","
                               `h]
                              "=>"
                              (Term.byTactic
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(group
                                   (Tactic.«tactic_<;>_»
                                    (Tactic.congr "congr" [] [])
                                    "<;>"
                                    (Tactic.injection "injection" `h []))
                                   [])]))))])))))
                       [])])))
                  [])])))
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
                    `le_transₓ
                    [(Term.app
                      `H
                      [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                      "⟩")]))
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
                         [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
                         ["with"
                          (Tactic.rcasesPat.tuple
                           "⟨"
                           [(Tactic.rcasesPatLo
                             (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')])
                             [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                           "⟩")])
                        "<;>"
                        (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
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
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                          "=>"
                          (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
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
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
                           (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
                           (Term.simpleBinder [`h] [])]
                          "=>"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group
                               (Tactic.«tactic_<;>_»
                                (Tactic.injection "injection" `h ["with" [`h]])
                                "<;>"
                                (Tactic.«tactic_<;>_»
                                 (Tactic.congr "congr" [] [])
                                 "<;>"
                                 (Tactic.injection "injection" `h [])))
                               [])]))))))
                       [])])))
                  [])])))
             [])])))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`α `r (Term.hole "_")] [])]
    "=>"
    («term_$__»
     (Term.app `induction_on [`b])
     "$"
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`β `s (Term.hole "_") `b0] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.skip "skip") [])
           (group
            (Tactic.change
             "change"
             («term_=_» (Term.app `cof [(Term.app `type [(Term.hole "_")])]) "=" (Term.hole "_"))
             [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `eq_of_forall_le_iff
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_cof_type) "," (Tactic.rwRule [] `le_cof_type)] "]")
             [])
            [])
           (group (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`H `S `hS])) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `le_transₓ
                   [(Term.app
                     `H
                     [(Set.«term{_|_}»
                       "{"
                       `a
                       "|"
                       (Term.app
                        `Sum.recOn
                        [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
                       "}")
                      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.cases'
                       "cases'"
                       [(Tactic.casesTarget [] `a)]
                       []
                       ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
                      [])
                     (group
                      (Tactic.«tactic·._»
                       "·"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.cases'
                            "cases'"
                            [(Tactic.casesTarget
                              []
                              (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
                            []
                            ["with" [(Lean.binderIdent `b)]])
                           [])
                          (group
                           (Tactic.rcases
                            "rcases"
                            [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                            ["with"
                             (Tactic.rcasesPat.tuple
                              "⟨"
                              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                               ","
                               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                               ","
                               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
                              "⟩")])
                           [])
                          (group
                           (Tactic.exact
                            "exact"
                            (Term.anonymousCtor
                             "⟨"
                             [(Term.app `Sum.inr [`b'])
                              ","
                              `bs
                              ","
                              (Term.byTactic
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                             "⟩"))
                           [])])))
                      [])
                     (group
                      (Tactic.«tactic·._»
                       "·"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.rcases
                            "rcases"
                            [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                            ["with"
                             (Tactic.rcasesPat.tuple
                              "⟨"
                              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                               ","
                               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                               ","
                               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                              "⟩")])
                           [])
                          (group
                           (Tactic.exact
                            "exact"
                            (Term.anonymousCtor
                             "⟨"
                             [(Term.app `Sum.inr [`b'])
                              ","
                              `bs
                              ","
                              (Term.byTactic
                               "by"
                               (Tactic.tacticSeq
                                (Tactic.tacticSeq1Indented
                                 [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
                             "⟩"))
                           [])])))
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
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`a] [])]
                         "=>"
                         (Term.match
                          "match"
                          []
                          [(Term.matchDiscr [] `a)]
                          []
                          "with"
                          (Term.matchAlts
                           [(Term.matchAlt
                             "|"
                             [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
                             "=>"
                             (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
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
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`a `b] [])]
                         "=>"
                         (Term.match
                          "match"
                          []
                          [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
                          []
                          "with"
                          (Term.matchAlts
                           [(Term.matchAlt
                             "|"
                             [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
                              ","
                              (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
                              ","
                              `h]
                             "=>"
                             (Term.byTactic
                              "by"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group
                                  (Tactic.«tactic_<;>_»
                                   (Tactic.congr "congr" [] [])
                                   "<;>"
                                   (Tactic.injection "injection" `h []))
                                  [])]))))])))))
                      [])])))
                 [])])))
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
                   `le_transₓ
                   [(Term.app
                     `H
                     [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
                      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
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
                        [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
                        ["with"
                         (Tactic.rcasesPat.tuple
                          "⟨"
                          [(Tactic.rcasesPatLo
                            (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')])
                            [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                          "⟩")])
                       "<;>"
                       (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
                      [])
                     (group
                      (Tactic.«tactic·._»
                       "·"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
                      [])
                     (group
                      (Tactic.«tactic·._»
                       "·"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
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
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                         "=>"
                         (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
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
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
                          (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
                          (Term.simpleBinder [`h] [])]
                         "=>"
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group
                              (Tactic.«tactic_<;>_»
                               (Tactic.injection "injection" `h ["with" [`h]])
                               "<;>"
                               (Tactic.«tactic_<;>_»
                                (Tactic.congr "congr" [] [])
                                "<;>"
                                (Tactic.injection "injection" `h [])))
                              [])]))))))
                      [])])))
                 [])])))
            [])]))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `induction_on [`b])
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`β `s (Term.hole "_") `b0] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.skip "skip") [])
         (group
          (Tactic.change
           "change"
           («term_=_» (Term.app `cof [(Term.app `type [(Term.hole "_")])]) "=" (Term.hole "_"))
           [])
          [])
         (group
          (Tactic.refine'
           "refine'"
           (Term.app
            `eq_of_forall_le_iff
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.hole "_")))]))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_cof_type) "," (Tactic.rwRule [] `le_cof_type)] "]")
           [])
          [])
         (group (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`H `S `hS])) [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `le_transₓ
                 [(Term.app
                   `H
                   [(Set.«term{_|_}»
                     "{"
                     `a
                     "|"
                     (Term.app
                      `Sum.recOn
                      [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
                     "}")
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.cases'
                     "cases'"
                     [(Tactic.casesTarget [] `a)]
                     []
                     ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.cases'
                          "cases'"
                          [(Tactic.casesTarget
                            []
                            (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
                          []
                          ["with" [(Lean.binderIdent `b)]])
                         [])
                        (group
                         (Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                          ["with"
                           (Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
                            "⟩")])
                         [])
                        (group
                         (Tactic.exact
                          "exact"
                          (Term.anonymousCtor
                           "⟨"
                           [(Term.app `Sum.inr [`b'])
                            ","
                            `bs
                            ","
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                           "⟩"))
                         [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                          ["with"
                           (Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                            "⟩")])
                         [])
                        (group
                         (Tactic.exact
                          "exact"
                          (Term.anonymousCtor
                           "⟨"
                           [(Term.app `Sum.inr [`b'])
                            ","
                            `bs
                            ","
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
                           "⟩"))
                         [])])))
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
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`a] [])]
                       "=>"
                       (Term.match
                        "match"
                        []
                        [(Term.matchDiscr [] `a)]
                        []
                        "with"
                        (Term.matchAlts
                         [(Term.matchAlt
                           "|"
                           [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
                           "=>"
                           (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
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
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`a `b] [])]
                       "=>"
                       (Term.match
                        "match"
                        []
                        [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
                        []
                        "with"
                        (Term.matchAlts
                         [(Term.matchAlt
                           "|"
                           [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
                            ","
                            (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
                            ","
                            `h]
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group
                                (Tactic.«tactic_<;>_»
                                 (Tactic.congr "congr" [] [])
                                 "<;>"
                                 (Tactic.injection "injection" `h []))
                                [])]))))])))))
                    [])])))
               [])])))
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
                 `le_transₓ
                 [(Term.app
                   `H
                   [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
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
                      [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
                      ["with"
                       (Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo
                          (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')])
                          [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                        "⟩")])
                     "<;>"
                     (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
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
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                       "=>"
                       (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
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
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
                        (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
                        (Term.simpleBinder [`h] [])]
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.«tactic_<;>_»
                             (Tactic.injection "injection" `h ["with" [`h]])
                             "<;>"
                             (Tactic.«tactic_<;>_»
                              (Tactic.congr "congr" [] [])
                              "<;>"
                              (Tactic.injection "injection" `h [])))
                            [])]))))))
                    [])])))
               [])])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`β `s (Term.hole "_") `b0] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.skip "skip") [])
        (group
         (Tactic.change
          "change"
          («term_=_» (Term.app `cof [(Term.app `type [(Term.hole "_")])]) "=" (Term.hole "_"))
          [])
         [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           `eq_of_forall_le_iff
           [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.hole "_")))]))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_cof_type) "," (Tactic.rwRule [] `le_cof_type)] "]")
          [])
         [])
        (group (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`H `S `hS])) [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.refine'
               "refine'"
               (Term.app
                `le_transₓ
                [(Term.app
                  `H
                  [(Set.«term{_|_}»
                    "{"
                    `a
                    "|"
                    (Term.app
                     `Sum.recOn
                     [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
                    "}")
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                 (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
              [])
             (group
              (Tactic.«tactic·._»
               "·"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.cases'
                    "cases'"
                    [(Tactic.casesTarget [] `a)]
                    []
                    ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
                   [])
                  (group
                   (Tactic.«tactic·._»
                    "·"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.cases'
                         "cases'"
                         [(Tactic.casesTarget
                           []
                           (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
                         []
                         ["with" [(Lean.binderIdent `b)]])
                        [])
                       (group
                        (Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                         ["with"
                          (Tactic.rcasesPat.tuple
                           "⟨"
                           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
                           "⟩")])
                        [])
                       (group
                        (Tactic.exact
                         "exact"
                         (Term.anonymousCtor
                          "⟨"
                          [(Term.app `Sum.inr [`b'])
                           ","
                           `bs
                           ","
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                          "⟩"))
                        [])])))
                   [])
                  (group
                   (Tactic.«tactic·._»
                    "·"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                         ["with"
                          (Tactic.rcasesPat.tuple
                           "⟨"
                           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                           "⟩")])
                        [])
                       (group
                        (Tactic.exact
                         "exact"
                         (Term.anonymousCtor
                          "⟨"
                          [(Term.app `Sum.inr [`b'])
                           ","
                           `bs
                           ","
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
                          "⟩"))
                        [])])))
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
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`a] [])]
                      "=>"
                      (Term.match
                       "match"
                       []
                       [(Term.matchDiscr [] `a)]
                       []
                       "with"
                       (Term.matchAlts
                        [(Term.matchAlt
                          "|"
                          [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
                          "=>"
                          (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
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
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`a `b] [])]
                      "=>"
                      (Term.match
                       "match"
                       []
                       [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
                       []
                       "with"
                       (Term.matchAlts
                        [(Term.matchAlt
                          "|"
                          [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
                           ","
                           (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
                           ","
                           `h]
                          "=>"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group
                               (Tactic.«tactic_<;>_»
                                (Tactic.congr "congr" [] [])
                                "<;>"
                                (Tactic.injection "injection" `h []))
                               [])]))))])))))
                   [])])))
              [])])))
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
                `le_transₓ
                [(Term.app
                  `H
                  [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                 (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
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
                     [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo
                         (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')])
                         [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                       "⟩")])
                    "<;>"
                    (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
                   [])
                  (group
                   (Tactic.«tactic·._»
                    "·"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
                   [])
                  (group
                   (Tactic.«tactic·._»
                    "·"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
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
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                      "=>"
                      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
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
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
                       (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
                       (Term.simpleBinder [`h] [])]
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.«tactic_<;>_»
                            (Tactic.injection "injection" `h ["with" [`h]])
                            "<;>"
                            (Tactic.«tactic_<;>_»
                             (Tactic.congr "congr" [] [])
                             "<;>"
                             (Tactic.injection "injection" `h [])))
                           [])]))))))
                   [])])))
              [])])))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.skip "skip") [])
      (group
       (Tactic.change "change" («term_=_» (Term.app `cof [(Term.app `type [(Term.hole "_")])]) "=" (Term.hole "_")) [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `eq_of_forall_le_iff
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_cof_type) "," (Tactic.rwRule [] `le_cof_type)] "]")
        [])
       [])
      (group (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`H `S `hS])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              `le_transₓ
              [(Term.app
                `H
                [(Set.«term{_|_}»
                  "{"
                  `a
                  "|"
                  (Term.app
                   `Sum.recOn
                   [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
                  "}")
                 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
               (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.cases'
                  "cases'"
                  [(Tactic.casesTarget [] `a)]
                  []
                  ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.cases'
                       "cases'"
                       [(Tactic.casesTarget
                         []
                         (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
                       []
                       ["with" [(Lean.binderIdent `b)]])
                      [])
                     (group
                      (Tactic.rcases
                       "rcases"
                       [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                       ["with"
                        (Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
                         "⟩")])
                      [])
                     (group
                      (Tactic.exact
                       "exact"
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.app `Sum.inr [`b'])
                         ","
                         `bs
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                        "⟩"))
                      [])])))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.rcases
                       "rcases"
                       [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                       ["with"
                        (Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                         "⟩")])
                      [])
                     (group
                      (Tactic.exact
                       "exact"
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.app `Sum.inr [`b'])
                         ","
                         `bs
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
                        "⟩"))
                      [])])))
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
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`a] [])]
                    "=>"
                    (Term.match
                     "match"
                     []
                     [(Term.matchDiscr [] `a)]
                     []
                     "with"
                     (Term.matchAlts
                      [(Term.matchAlt
                        "|"
                        [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
                        "=>"
                        (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
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
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`a `b] [])]
                    "=>"
                    (Term.match
                     "match"
                     []
                     [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
                     []
                     "with"
                     (Term.matchAlts
                      [(Term.matchAlt
                        "|"
                        [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
                         ","
                         (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
                         ","
                         `h]
                        "=>"
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.«tactic_<;>_»
                              (Tactic.congr "congr" [] [])
                              "<;>"
                              (Tactic.injection "injection" `h []))
                             [])]))))])))))
                 [])])))
            [])])))
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
              `le_transₓ
              [(Term.app
                `H
                [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
                 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
               (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
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
                   [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
                   ["with"
                    (Tactic.rcasesPat.tuple
                     "⟨"
                     [(Tactic.rcasesPatLo
                       (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')])
                       [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                     "⟩")])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
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
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                    "=>"
                    (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
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
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
                     (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
                     (Term.simpleBinder [`h] [])]
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.«tactic_<;>_»
                          (Tactic.injection "injection" `h ["with" [`h]])
                          "<;>"
                          (Tactic.«tactic_<;>_»
                           (Tactic.congr "congr" [] [])
                           "<;>"
                           (Tactic.injection "injection" `h [])))
                         [])]))))))
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `le_transₓ
         [(Term.app
           `H
           [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
          (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
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
              [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')])
                  [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                "⟩")])
             "<;>"
             (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
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
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
               "=>"
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
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
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
                (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
                (Term.simpleBinder [`h] [])]
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic_<;>_»
                     (Tactic.injection "injection" `h ["with" [`h]])
                     "<;>"
                     (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
                    [])]))))))
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
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
           (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
           (Term.simpleBinder [`h] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.«tactic_<;>_»
                (Tactic.injection "injection" `h ["with" [`h]])
                "<;>"
                (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
               [])]))))))
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
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩") (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩") (Term.simpleBinder [`h] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.«tactic_<;>_»
           (Tactic.injection "injection" `h ["with" [`h]])
           "<;>"
           (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.anonymousCtor "⟨" [`a "," `h₁] "⟩") (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩") (Term.simpleBinder [`h] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.«tactic_<;>_»
          (Tactic.injection "injection" `h ["with" [`h]])
          "<;>"
          (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.injection "injection" `h ["with" [`h]])
        "<;>"
        (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
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
   (Tactic.injection "injection" `h ["with" [`h]])
   "<;>"
   (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.injection "injection" `h [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.injection', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.injection "injection" `h ["with" [`h]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.injection', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," `h₂] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.anonymousCtor "⟨" [`a "," `h₁] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
          "=>"
          (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
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
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
     "=>"
     (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
    "=>"
    (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`a "," `h] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
           "⟩")])
        "<;>"
        (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
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
    (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b' "," `bs "," `h] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic_<;>_»
   (Tactic.rcases
    "rcases"
    [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
    ["with"
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
      "⟩")])
   "<;>"
   (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] (Term.app `hS [(Term.app `Sum.inr [`a])]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a') "|" (Tactic.rcasesPat.one `b')]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hS [(Term.app `Sum.inr [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sum.inr [`a])
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
  `Sum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Sum.inr [`a]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `le_transₓ
    [(Term.app
      `H
      [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
     (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `le_transₓ
   [(Term.app
     `H
     [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app
   `H
   [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `Sum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `H
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `H
   [(Term.paren "(" [(Set.Data.Set.Basic.«term_⁻¹'_» `Sum.inr " ⁻¹' " `S) []] ")")
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_transₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         `le_transₓ
         [(Term.app
           `H
           [(Set.«term{_|_}»
             "{"
             `a
             "|"
             (Term.app
              `Sum.recOn
              [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
             "}")
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
          (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] `a)]
             []
             ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.cases'
                  "cases'"
                  [(Tactic.casesTarget [] (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
                  []
                  ["with" [(Lean.binderIdent `b)]])
                 [])
                (group
                 (Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                  ["with"
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
                    "⟩")])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `Sum.inr [`b'])
                    ","
                    `bs
                    ","
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                   "⟩"))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] (Term.app `hS [`b]))]
                  ["with"
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
                    "⟩")])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `Sum.inr [`b'])
                    ","
                    `bs
                    ","
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
                   "⟩"))
                 [])])))
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
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`a] [])]
               "=>"
               (Term.match
                "match"
                []
                [(Term.matchDiscr [] `a)]
                []
                "with"
                (Term.matchAlts
                 [(Term.matchAlt
                   "|"
                   [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
                   "=>"
                   (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
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
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`a `b] [])]
               "=>"
               (Term.match
                "match"
                []
                [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
                []
                "with"
                (Term.matchAlts
                 [(Term.matchAlt
                   "|"
                   [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
                    ","
                    (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
                    ","
                    `h]
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h []))
                        [])]))))])))))
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
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`a `b] [])]
          "=>"
          (Term.match
           "match"
           []
           [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
           []
           "with"
           (Term.matchAlts
            [(Term.matchAlt
              "|"
              [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
               ","
               (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
               ","
               `h]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h []))
                   [])]))))])))))
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
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`a `b] [])]
     "=>"
     (Term.match
      "match"
      []
      [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
      []
      "with"
      (Term.matchAlts
       [(Term.matchAlt
         "|"
         [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
          ","
          (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
          ","
          `h]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h []))
              [])]))))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a `b] [])]
    "=>"
    (Term.match
     "match"
     []
     [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
     []
     "with"
     (Term.matchAlts
      [(Term.matchAlt
        "|"
        [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
         ","
         (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
         ","
         `h]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h []))
             [])]))))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.match
   "match"
   []
   [(Term.matchDiscr [] `a) "," (Term.matchDiscr [] `b)]
   []
   "with"
   (Term.matchAlts
    [(Term.matchAlt
      "|"
      [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
       ","
       (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
       ","
       `h]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h []))
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
     [(group (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.injection "injection" `h [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.injection', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h₂] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sum.inr [`b])
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
  `Sum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`a]) "," `h₁] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sum.inr [`a])
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
  `Sum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchDiscr', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchDiscr', expected 'Lean.Parser.Term.matchDiscr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchDiscr', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchDiscr', expected 'Lean.Parser.Term.matchDiscr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`a] [])]
          "=>"
          (Term.match
           "match"
           []
           [(Term.matchDiscr [] `a)]
           []
           "with"
           (Term.matchAlts
            [(Term.matchAlt
              "|"
              [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
              "=>"
              (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
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
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`a] [])]
     "=>"
     (Term.match
      "match"
      []
      [(Term.matchDiscr [] `a)]
      []
      "with"
      (Term.matchAlts
       [(Term.matchAlt
         "|"
         [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
         "=>"
         (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a] [])]
    "=>"
    (Term.match
     "match"
     []
     [(Term.matchDiscr [] `a)]
     []
     "with"
     (Term.matchAlts
      [(Term.matchAlt
        "|"
        [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
        "=>"
        (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.match
   "match"
   []
   [(Term.matchDiscr [] `a)]
   []
   "with"
   (Term.matchAlts
    [(Term.matchAlt
      "|"
      [(Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")]
      "=>"
      (Term.anonymousCtor "⟨" [`b "," `h] "⟩"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.match', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.match', expected 'Lean.Parser.Term.match.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," `h] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.app `Sum.inr [`b]) "," `h] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sum.inr [`b])
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
  `Sum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchDiscr', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchDiscr', expected 'Lean.Parser.Term.matchDiscr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.cases' "cases'" [(Tactic.casesTarget [] `a)] [] ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
             []
             ["with" [(Lean.binderIdent `b)]])
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `hS [`b]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
               "⟩")])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `Sum.inr [`b'])
               ","
               `bs
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
              "⟩"))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `hS [`b]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `Sum.inr [`b'])
               ","
               `bs
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
              "⟩"))
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
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `hS [`b]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `Sum.inr [`b'])
          ","
          `bs
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
         "⟩"))
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
   (Term.anonymousCtor
    "⟨"
    [(Term.app `Sum.inr [`b'])
     ","
     `bs
     ","
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `Sum.inr [`b'])
    ","
    `bs
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sum.inr [`b'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Sum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] (Term.app `hS [`b]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
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
  (Term.app `hS [`b])
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
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
        []
        ["with" [(Lean.binderIdent `b)]])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `hS [`b]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
          "⟩")])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `Sum.inr [`b'])
          ","
          `bs
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
         "⟩"))
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
   (Term.anonymousCtor
    "⟨"
    [(Term.app `Sum.inr [`b'])
     ","
     `bs
     ","
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `Sum.inr [`b'])
    ","
    `bs
    ","
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sum.inr [`b'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Sum.inr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] (Term.app `hS [`b]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b')]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bs)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'antiquot'
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
  (Term.app `hS [`b])
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
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases'
   "cases'"
   [(Tactic.casesTarget [] (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0]))]
   []
   ["with" [(Lean.binderIdent `b)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1")) [`b0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `type_ne_zero_iff_nonempty "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `type_ne_zero_iff_nonempty
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases' "cases'" [(Tactic.casesTarget [] `a)] [] ["with" [(Lean.binderIdent `a) (Lean.binderIdent `b)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `le_transₓ
    [(Term.app
      `H
      [(Set.«term{_|_}»
        "{"
        `a
        "|"
        (Term.app
         `Sum.recOn
         [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
        "}")
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
     (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `le_transₓ
   [(Term.app
     `H
     [(Set.«term{_|_}»
       "{"
       `a
       "|"
       (Term.app
        `Sum.recOn
        [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
       "}")
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app
   `H
   [(Set.«term{_|_}»
     "{"
     `a
     "|"
     (Term.app `Sum.recOn [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
     "}")
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}»
   "{"
   `a
   "|"
   (Term.app `Sum.recOn [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Sum.recOn [`a (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")") `S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [(«term∅» "∅") [(Term.typeAscription ":" (Term.app `Set [`α]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term∅» "∅")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∅»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Sum.recOn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
@[ simp ]
  theorem
    cof_add
    ( a b : Ordinal ) : b ≠ 0 → cof a + b = cof b
    :=
      induction_on a
        $
        fun
          α r _
            =>
            induction_on b
              $
              fun
                β s _ b0
                  =>
                  by
                    skip
                      change cof type _ = _
                      refine' eq_of_forall_le_iff fun c => _
                      rw [ le_cof_type , le_cof_type ]
                      constructor <;> intro H S hS
                      ·
                        refine' le_transₓ H { a | Sum.recOn a ( ∅ : Set α ) S } fun a => _ ⟨ ⟨ _ , _ ⟩ ⟩
                          ·
                            cases' a with a b
                              ·
                                cases' type_ne_zero_iff_nonempty . 1 b0 with b
                                  rcases hS b with ⟨ b' , bs , _ ⟩
                                  exact ⟨ Sum.inr b' , bs , by simp ⟩
                              · rcases hS b with ⟨ b' , bs , h ⟩ exact ⟨ Sum.inr b' , bs , by simp [ h ] ⟩
                          · exact fun a => match a with | ⟨ Sum.inr b , h ⟩ => ⟨ b , h ⟩
                          ·
                            exact
                              fun
                                a b
                                  =>
                                  match
                                    a , b
                                    with
                                    | ⟨ Sum.inr a , h₁ ⟩ , ⟨ Sum.inr b , h₂ ⟩ , h => by congr <;> injection h
                      ·
                        refine' le_transₓ H Sum.inr ⁻¹' S fun a => _ ⟨ ⟨ _ , _ ⟩ ⟩
                          ·
                            rcases hS Sum.inr a with ⟨ a' | b' , bs , h ⟩ <;> simp at h
                              · cases h
                              · exact ⟨ b' , bs , h ⟩
                          · exact fun ⟨ a , h ⟩ => ⟨ _ , h ⟩
                          · exact fun ⟨ a , h₁ ⟩ ⟨ b , h₂ ⟩ h => by injection h with h <;> congr <;> injection h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `cof_cof [])
  (Command.declSig
   [(Term.explicitBinder "(" [`o] [":" `Ordinal] [] ")")]
   (Term.typeSpec ":" («term_=_» (Term.app `cof [(Term.proj (Term.app `cof [`o]) "." `ord)]) "=" (Term.app `cof [`o]))))
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.app
     `le_antisymmₓ
     [(Term.app
       `le_transₓ
       [(Term.app `cof_le_card [(Term.hole "_")])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))])])
    "$"
    («term_$__»
     (Term.app `induction_on [`o])
     "$"
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`α `r (Term.hole "_")] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`S "," `hS "," `e₁] "⟩")
                []
                []
                ":="
                (Term.app `ord_cof_eq [`r])))
              []
              (Term.let
               "let"
               (Term.letDecl
                (Term.letPatDecl
                 (Term.anonymousCtor "⟨" [`T "," `hT "," `e₂] "⟩")
                 []
                 []
                 ":="
                 (Term.app `cof_eq [(Term.app `Subrel [`r `S])])))
               []
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
                    [])
                   (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
                   (group
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `le_transₓ
                      [(Term.app
                        `cof_type_le
                        [(Set.«term{_|_}»
                          "{"
                          `a
                          "|"
                          («term∃_,_»
                           "∃"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
                           ","
                           (Init.Core.«term_∈_»
                            (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
                            " ∈ "
                            `T))
                          "}")
                         (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                        "⟩")]))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget [] (Term.app `hS [`a]))]
                          ["with"
                           (Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
                            "⟩")])
                         [])
                        (group
                         (Tactic.rcases
                          "rcases"
                          [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
                          ["with"
                           (Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo
                              (Tactic.rcasesPatMed
                               [(Tactic.rcasesPat.tuple
                                 "⟨"
                                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                                  ","
                                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                                 "⟩")])
                              [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
                            "⟩")])
                         [])
                        (group
                         (Tactic.exact
                          "exact"
                          (Term.anonymousCtor
                           "⟨"
                           [`c
                            ","
                            (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩")
                            ","
                            (Term.app `IsOrderConnected.neg_trans [`cs `br])]
                           "⟩"))
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
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                            "=>"
                            (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                             (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                             (Term.simpleBinder [`h] [])]
                            "=>"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.«tactic_<;>_»
                                  (Tactic.injection "injection" `h ["with" [`h]])
                                  "<;>"
                                  (Tactic.«tactic_<;>_»
                                   (Tactic.congr "congr" [] [])
                                   "<;>"
                                   (Tactic.injection "injection" `h [])))
                                 [])]))))))
                         [])])))
                    [])]))))))
            [])])))))))
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
  («term_$__»
   (Term.app
    `le_antisymmₓ
    [(Term.app
      `le_transₓ
      [(Term.app `cof_le_card [(Term.hole "_")])
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))])])
   "$"
   («term_$__»
    (Term.app `induction_on [`o])
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`α `r (Term.hole "_")] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.exact
            "exact"
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor "⟨" [`S "," `hS "," `e₁] "⟩")
               []
               []
               ":="
               (Term.app `ord_cof_eq [`r])))
             []
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`T "," `hT "," `e₂] "⟩")
                []
                []
                ":="
                (Term.app `cof_eq [(Term.app `Subrel [`r `S])])))
              []
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
                   [])
                  (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
                  (group
                   (Tactic.refine'
                    "refine'"
                    (Term.app
                     `le_transₓ
                     [(Term.app
                       `cof_type_le
                       [(Set.«term{_|_}»
                         "{"
                         `a
                         "|"
                         («term∃_,_»
                          "∃"
                          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
                          ","
                          (Init.Core.«term_∈_»
                           (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
                           " ∈ "
                           `T))
                         "}")
                        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                       "⟩")]))
                   [])
                  (group
                   (Tactic.«tactic·._»
                    "·"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget [] (Term.app `hS [`a]))]
                         ["with"
                          (Tactic.rcasesPat.tuple
                           "⟨"
                           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
                           "⟩")])
                        [])
                       (group
                        (Tactic.rcases
                         "rcases"
                         [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
                         ["with"
                          (Tactic.rcasesPat.tuple
                           "⟨"
                           [(Tactic.rcasesPatLo
                             (Tactic.rcasesPatMed
                              [(Tactic.rcasesPat.tuple
                                "⟨"
                                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                                 ","
                                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                                "⟩")])
                             [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
                           "⟩")])
                        [])
                       (group
                        (Tactic.exact
                         "exact"
                         (Term.anonymousCtor
                          "⟨"
                          [`c
                           ","
                           (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩")
                           ","
                           (Term.app `IsOrderConnected.neg_trans [`cs `br])]
                          "⟩"))
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
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                           "=>"
                           (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                            (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                            (Term.simpleBinder [`h] [])]
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group
                                (Tactic.«tactic_<;>_»
                                 (Tactic.injection "injection" `h ["with" [`h]])
                                 "<;>"
                                 (Tactic.«tactic_<;>_»
                                  (Tactic.congr "congr" [] [])
                                  "<;>"
                                  (Tactic.injection "injection" `h [])))
                                [])]))))))
                        [])])))
                   [])]))))))
           [])])))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `induction_on [`o])
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`α `r (Term.hole "_")] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.exact
           "exact"
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl (Term.anonymousCtor "⟨" [`S "," `hS "," `e₁] "⟩") [] [] ":=" (Term.app `ord_cof_eq [`r])))
            []
            (Term.let
             "let"
             (Term.letDecl
              (Term.letPatDecl
               (Term.anonymousCtor "⟨" [`T "," `hT "," `e₂] "⟩")
               []
               []
               ":="
               (Term.app `cof_eq [(Term.app `Subrel [`r `S])])))
             []
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
                  [])
                 (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
                 (group
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `le_transₓ
                    [(Term.app
                      `cof_type_le
                      [(Set.«term{_|_}»
                        "{"
                        `a
                        "|"
                        («term∃_,_»
                         "∃"
                         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
                         ","
                         (Init.Core.«term_∈_»
                          (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
                          " ∈ "
                          `T))
                        "}")
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")]
                      "⟩")]))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.rcases
                        "rcases"
                        [(Tactic.casesTarget [] (Term.app `hS [`a]))]
                        ["with"
                         (Tactic.rcasesPat.tuple
                          "⟨"
                          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
                          "⟩")])
                       [])
                      (group
                       (Tactic.rcases
                        "rcases"
                        [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
                        ["with"
                         (Tactic.rcasesPat.tuple
                          "⟨"
                          [(Tactic.rcasesPatLo
                            (Tactic.rcasesPatMed
                             [(Tactic.rcasesPat.tuple
                               "⟨"
                               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                                ","
                                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                               "⟩")])
                            [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                           ","
                           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
                          "⟩")])
                       [])
                      (group
                       (Tactic.exact
                        "exact"
                        (Term.anonymousCtor
                         "⟨"
                         [`c
                          ","
                          (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩")
                          ","
                          (Term.app `IsOrderConnected.neg_trans [`cs `br])]
                         "⟩"))
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
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                          "=>"
                          (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                           (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                           (Term.simpleBinder [`h] [])]
                          "=>"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group
                               (Tactic.«tactic_<;>_»
                                (Tactic.injection "injection" `h ["with" [`h]])
                                "<;>"
                                (Tactic.«tactic_<;>_»
                                 (Tactic.congr "congr" [] [])
                                 "<;>"
                                 (Tactic.injection "injection" `h [])))
                               [])]))))))
                       [])])))
                  [])]))))))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`α `r (Term.hole "_")] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.exact
          "exact"
          (Term.let
           "let"
           (Term.letDecl
            (Term.letPatDecl (Term.anonymousCtor "⟨" [`S "," `hS "," `e₁] "⟩") [] [] ":=" (Term.app `ord_cof_eq [`r])))
           []
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`T "," `hT "," `e₂] "⟩")
              []
              []
              ":="
              (Term.app `cof_eq [(Term.app `Subrel [`r `S])])))
            []
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
                 [])
                (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `le_transₓ
                   [(Term.app
                     `cof_type_le
                     [(Set.«term{_|_}»
                       "{"
                       `a
                       "|"
                       («term∃_,_»
                        "∃"
                        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
                        ","
                        (Init.Core.«term_∈_»
                         (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
                         " ∈ "
                         `T))
                       "}")
                      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.rcases
                       "rcases"
                       [(Tactic.casesTarget [] (Term.app `hS [`a]))]
                       ["with"
                        (Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
                         "⟩")])
                      [])
                     (group
                      (Tactic.rcases
                       "rcases"
                       [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
                       ["with"
                        (Tactic.rcasesPat.tuple
                         "⟨"
                         [(Tactic.rcasesPatLo
                           (Tactic.rcasesPatMed
                            [(Tactic.rcasesPat.tuple
                              "⟨"
                              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                               ","
                               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                              "⟩")])
                           [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                          ","
                          (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
                         "⟩")])
                      [])
                     (group
                      (Tactic.exact
                       "exact"
                       (Term.anonymousCtor
                        "⟨"
                        [`c
                         ","
                         (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩")
                         ","
                         (Term.app `IsOrderConnected.neg_trans [`cs `br])]
                        "⟩"))
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
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                         "=>"
                         (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                          (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                          (Term.simpleBinder [`h] [])]
                         "=>"
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group
                              (Tactic.«tactic_<;>_»
                               (Tactic.injection "injection" `h ["with" [`h]])
                               "<;>"
                               (Tactic.«tactic_<;>_»
                                (Tactic.congr "congr" [] [])
                                "<;>"
                                (Tactic.injection "injection" `h [])))
                              [])]))))))
                      [])])))
                 [])]))))))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl (Term.anonymousCtor "⟨" [`S "," `hS "," `e₁] "⟩") [] [] ":=" (Term.app `ord_cof_eq [`r])))
         []
         (Term.let
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Term.anonymousCtor "⟨" [`T "," `hT "," `e₂] "⟩")
            []
            []
            ":="
            (Term.app `cof_eq [(Term.app `Subrel [`r `S])])))
          []
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
               [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `le_transₓ
                 [(Term.app
                   `cof_type_le
                   [(Set.«term{_|_}»
                     "{"
                     `a
                     "|"
                     («term∃_,_»
                      "∃"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
                      ","
                      (Init.Core.«term_∈_»
                       (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
                       " ∈ "
                       `T))
                     "}")
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
                  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] (Term.app `hS [`a]))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
                     ["with"
                      (Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo
                         (Tactic.rcasesPatMed
                          [(Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                            "⟩")])
                         [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
                       "⟩")])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.anonymousCtor
                      "⟨"
                      [`c
                       ","
                       (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩")
                       ","
                       (Term.app `IsOrderConnected.neg_trans [`cs `br])]
                      "⟩"))
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
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                       "=>"
                       (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                        (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                        (Term.simpleBinder [`h] [])]
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.«tactic_<;>_»
                             (Tactic.injection "injection" `h ["with" [`h]])
                             "<;>"
                             (Tactic.«tactic_<;>_»
                              (Tactic.congr "congr" [] [])
                              "<;>"
                              (Tactic.injection "injection" `h [])))
                            [])]))))))
                    [])])))
               [])]))))))
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
   (Term.let
    "let"
    (Term.letDecl
     (Term.letPatDecl (Term.anonymousCtor "⟨" [`S "," `hS "," `e₁] "⟩") [] [] ":=" (Term.app `ord_cof_eq [`r])))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letPatDecl
       (Term.anonymousCtor "⟨" [`T "," `hT "," `e₂] "⟩")
       []
       []
       ":="
       (Term.app `cof_eq [(Term.app `Subrel [`r `S])])))
     []
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
          [])
         (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
         (group
          (Tactic.refine'
           "refine'"
           (Term.app
            `le_transₓ
            [(Term.app
              `cof_type_le
              [(Set.«term{_|_}»
                "{"
                `a
                "|"
                («term∃_,_»
                 "∃"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
                 ","
                 (Init.Core.«term_∈_»
                  (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
                  " ∈ "
                  `T))
                "}")
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
             (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `hS [`a]))]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo
                    (Tactic.rcasesPatMed
                     [(Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                       "⟩")])
                    [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [`c
                  ","
                  (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩")
                  ","
                  (Term.app `IsOrderConnected.neg_trans [`cs `br])]
                 "⟩"))
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
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                  "=>"
                  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                   (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                   (Term.simpleBinder [`h] [])]
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.«tactic_<;>_»
                        (Tactic.injection "injection" `h ["with" [`h]])
                        "<;>"
                        (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
                       [])]))))))
               [])])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl (Term.anonymousCtor "⟨" [`S "," `hS "," `e₁] "⟩") [] [] ":=" (Term.app `ord_cof_eq [`r])))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letPatDecl
      (Term.anonymousCtor "⟨" [`T "," `hT "," `e₂] "⟩")
      []
      []
      ":="
      (Term.app `cof_eq [(Term.app `Subrel [`r `S])])))
    []
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
          [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
         [])
        (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           `le_transₓ
           [(Term.app
             `cof_type_le
             [(Set.«term{_|_}»
               "{"
               `a
               "|"
               («term∃_,_»
                "∃"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
                ","
                (Init.Core.«term_∈_»
                 (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
                 " ∈ "
                 `T))
               "}")
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
            (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
         [])
        (group
         (Tactic.«tactic·._»
          "·"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `hS [`a]))]
               ["with"
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
                 "⟩")])
              [])
             (group
              (Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
               ["with"
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo
                   (Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                      "⟩")])
                   [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
                 "⟩")])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`c "," (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩") "," (Term.app `IsOrderConnected.neg_trans [`cs `br])]
                "⟩"))
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
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                 "=>"
                 (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                  (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                  (Term.simpleBinder [`h] [])]
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.«tactic_<;>_»
                       (Tactic.injection "injection" `h ["with" [`h]])
                       "<;>"
                       (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
                      [])]))))))
              [])])))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Term.anonymousCtor "⟨" [`T "," `hT "," `e₂] "⟩")
     []
     []
     ":="
     (Term.app `cof_eq [(Term.app `Subrel [`r `S])])))
   []
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
        [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `le_transₓ
          [(Term.app
            `cof_type_le
            [(Set.«term{_|_}»
              "{"
              `a
              "|"
              («term∃_,_»
               "∃"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
               ","
               (Init.Core.«term_∈_»
                (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
                " ∈ "
                `T))
              "}")
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
           (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `hS [`a]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed
                   [(Tactic.rcasesPat.tuple
                     "⟨"
                     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                      ","
                      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                     "⟩")])
                  [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`c "," (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩") "," (Term.app `IsOrderConnected.neg_trans [`cs `br])]
               "⟩"))
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
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                "=>"
                (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                 (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                 (Term.simpleBinder [`h] [])]
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic_<;>_»
                      (Tactic.injection "injection" `h ["with" [`h]])
                      "<;>"
                      (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
                     [])]))))))
             [])])))
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`e₂] []))])
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `e₂)] "]") []) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `le_transₓ
         [(Term.app
           `cof_type_le
           [(Set.«term{_|_}»
             "{"
             `a
             "|"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
              ","
              (Init.Core.«term_∈_»
               (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
               " ∈ "
               `T))
             "}")
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
          (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `hS [`a]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo
                 (Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
                    "⟩")])
                 [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [`c "," (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩") "," (Term.app `IsOrderConnected.neg_trans [`cs `br])]
              "⟩"))
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
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
               "=>"
               (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
                (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
                (Term.simpleBinder [`h] [])]
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic_<;>_»
                     (Tactic.injection "injection" `h ["with" [`h]])
                     "<;>"
                     (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
                    [])]))))))
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
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
           (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
           (Term.simpleBinder [`h] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.«tactic_<;>_»
                (Tactic.injection "injection" `h ["with" [`h]])
                "<;>"
                (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
               [])]))))))
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
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩") (Term.anonymousCtor "⟨" [`b "," `hb] "⟩") (Term.simpleBinder [`h] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.«tactic_<;>_»
           (Tactic.injection "injection" `h ["with" [`h]])
           "<;>"
           (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.anonymousCtor "⟨" [`a "," `ha] "⟩") (Term.anonymousCtor "⟨" [`b "," `hb] "⟩") (Term.simpleBinder [`h] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.«tactic_<;>_»
          (Tactic.injection "injection" `h ["with" [`h]])
          "<;>"
          (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.injection "injection" `h ["with" [`h]])
        "<;>"
        (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
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
   (Tactic.injection "injection" `h ["with" [`h]])
   "<;>"
   (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_» (Tactic.congr "congr" [] []) "<;>" (Tactic.injection "injection" `h []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.injection "injection" `h [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.injection', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.injection "injection" `h ["with" [`h]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.injection', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," `hb] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hb
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.anonymousCtor "⟨" [`a "," `ha] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ha
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
          "=>"
          (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
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
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
     "=>"
     (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
    "=>"
    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩") "," `h.snd] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h.snd
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`a "," `h.fst] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h.fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`a "," `h] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `hS [`a]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo
            (Tactic.rcasesPatMed
             [(Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
               "⟩")])
            [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [`c "," (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩") "," (Term.app `IsOrderConnected.neg_trans [`cs `br])]
         "⟩"))
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
   (Term.anonymousCtor
    "⟨"
    [`c "," (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩") "," (Term.app `IsOrderConnected.neg_trans [`cs `br])]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`c "," (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩") "," (Term.app `IsOrderConnected.neg_trans [`cs `br])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IsOrderConnected.neg_trans [`cs `br])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `br
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `cs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsOrderConnected.neg_trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`cS "," `cT] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `cT
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `cS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo
       (Tactic.rcasesPatMed
        [(Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cS)]) [])]
          "⟩")])
       [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cT)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `cs)]) [])]
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
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
  (Term.app `hT [(Term.anonymousCtor "⟨" [`b "," `bS] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`b "," `bS] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hT
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] (Term.app `hS [`a]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `bS)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `br)]) [])]
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
  (Term.app `hS [`a])
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
  `hS
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `le_transₓ
    [(Term.app
      `cof_type_le
      [(Set.«term{_|_}»
        "{"
        `a
        "|"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
         ","
         (Init.Core.«term_∈_»
          (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
          " ∈ "
          `T))
        "}")
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
     (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `le_transₓ
   [(Term.app
     `cof_type_le
     [(Set.«term{_|_}»
       "{"
       `a
       "|"
       («term∃_,_»
        "∃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
        ","
        (Init.Core.«term_∈_»
         (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
         " ∈ "
         `T))
       "}")
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app
   `cof_type_le
   [(Set.«term{_|_}»
     "{"
     `a
     "|"
     («term∃_,_»
      "∃"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
      ","
      (Init.Core.«term_∈_»
       (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
       " ∈ "
       `T))
     "}")
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}»
   "{"
   `a
   "|"
   («term∃_,_»
    "∃"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
    ","
    (Init.Core.«term_∈_» (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")") " ∈ " `T))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] []))
   ","
   (Init.Core.«term_∈_» (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")") " ∈ " `T))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")") " ∈ " `T)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `T
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren "(" [(Term.app `Subtype.mk [`a `h]) [(Term.typeAscription ":" `S)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `Subtype.mk [`a `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
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
  `Subtype.mk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
@[ simp ]
  theorem
    cof_cof
    ( o : Ordinal ) : cof cof o . ord = cof o
    :=
      le_antisymmₓ le_transₓ cof_le_card _ by simp
        $
        induction_on o
          $
          fun
            α r _
              =>
              by
                exact
                  let
                    ⟨ S , hS , e₁ ⟩ := ord_cof_eq r
                    let
                      ⟨ T , hT , e₂ ⟩ := cof_eq Subrel r S
                      by
                        rw [ e₁ ] at e₂
                          rw [ ← e₂ ]
                          refine'
                            le_transₓ cof_type_le { a | ∃ h , ( Subtype.mk a h : S ) ∈ T } fun a => _ ⟨ ⟨ _ , _ ⟩ ⟩
                          ·
                            rcases hS a with ⟨ b , bS , br ⟩
                              rcases hT ⟨ b , bS ⟩ with ⟨ ⟨ c , cS ⟩ , cT , cs ⟩
                              exact ⟨ c , ⟨ cS , cT ⟩ , IsOrderConnected.neg_trans cs br ⟩
                          · exact fun ⟨ a , h ⟩ => ⟨ ⟨ a , h.fst ⟩ , h.snd ⟩
                          · exact fun ⟨ a , ha ⟩ ⟨ b , hb ⟩ h => by injection h with h <;> congr <;> injection h

theorem omega_le_cof {o} : ω ≤ cof o ↔ is_limit o := by
  rcases zero_or_succ_or_limit o with (rfl | ⟨o, rfl⟩ | l)
  ·
    simp [not_zero_is_limit, Cardinal.omega_ne_zero]
  ·
    simp [not_succ_is_limit, Cardinal.one_lt_omega]
  ·
    simp [l]
    refine' le_of_not_ltₓ fun h => _
    cases' Cardinal.lt_omega.1 h with n e
    have := cof_cof o
    rw [e, ord_nat] at this
    cases n
    ·
      simp at e
      simpa [e, not_zero_is_limit] using l
    ·
      rw [← nat_cast_succ, cof_succ] at this
      rw [← this, cof_eq_one_iff_is_succ] at e
      rcases e with ⟨a, rfl⟩
      exact not_succ_is_limit _ l

@[simp]
theorem cof_omega : cof omega = ω :=
  le_antisymmₓ
    (by
      rw [← card_omega] <;> apply cof_le_card)
    (omega_le_cof.2 omega_is_limit)

theorem cof_eq' (r : α → α → Prop) [IsWellOrder α r] (h : is_limit (type r)) :
    ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ # S = cof (type r) :=
  let ⟨S, H, e⟩ := cof_eq r
  ⟨S, fun a =>
    let a' := enum r _ (h.2 _ (typein_lt_type r a))
    let ⟨b, h, ab⟩ := H a'
    ⟨b, h,
      (IsOrderConnected.conn a b a' $
            (typein_lt_typein r).1
              (by
                rw [typein_enum] <;> apply Ordinal.lt_succ_self)).resolve_right
        ab⟩,
    e⟩

theorem cof_sup_le_lift {ι} (f : ι → Ordinal) (H : ∀ i, f i < sup f) : cof (sup f) ≤ (# ι).lift := by
  generalize e : sup f = o
  refine' Ordinal.induction_on o _ e
  intros α r _ e'
  rw [e'] at H
  refine' le_transₓ (cof_type_le (Set.Range fun i => enum r _ (H i)) _) ⟨embedding.of_surjective _ _⟩
  ·
    intro a
    by_contra h
    apply not_le_of_lt (typein_lt_type r a)
    rw [← e', sup_le]
    intro i
    have h : ∀ x : ι, r (enum r (f x) _) a := by
      simpa using h
    simpa only [typein_enum] using le_of_ltₓ ((typein_lt_typein r).2 (h i))
  ·
    exact fun i => ⟨_, Set.mem_range_self i.1⟩
  ·
    intro a
    rcases a with ⟨_, i, rfl⟩
    exact
      ⟨⟨i⟩, by
        simp ⟩

theorem cof_sup_le {ι} (f : ι → Ordinal) (H : ∀ i, f i < sup.{u, u} f) : cof (sup.{u, u} f) ≤ # ι := by
  simpa using cof_sup_le_lift.{u, u} f H

theorem cof_bsup_le_lift {o : Ordinal} :
    ∀ f : ∀, ∀ a < o, ∀, Ordinal, (∀ i h, f i h < bsup o f) → cof (bsup o f) ≤ o.card.lift :=
  induction_on o $ fun α r _ f H => by
    rw [bsup_type] <;> refine' cof_sup_le_lift _ _ <;> rw [← bsup_type] <;> intro a <;> apply H

theorem cof_bsup_le {o : Ordinal} :
    ∀ f : ∀, ∀ a < o, ∀, Ordinal, (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card :=
  induction_on o $ fun α r _ f H => by
    simpa using cof_bsup_le_lift.{u, u} f H

@[simp]
theorem cof_univ : cof univ.{u, v} = Cardinal.univ :=
  le_antisymmₓ (cof_le_card _)
    (by
      refine' le_of_forall_lt fun c h => _
      rcases lt_univ'.1 h with ⟨c, rfl⟩
      rcases@cof_eq Ordinal.{u} (· < ·) _ with ⟨S, H, Se⟩
      rw [univ, ← lift_cof, ← Cardinal.lift_lift, Cardinal.lift_lt, ← Se]
      refine' lt_of_not_geₓ fun h => _
      cases' Cardinal.lift_down h with a e
      refine' Quotientₓ.induction_on a (fun α e => _) e
      cases' Quotientₓ.exact e with f
      have f := equiv.ulift.symm.trans f
      let g := fun a => (f a).1
      let o := succ (sup.{u, u} g)
      rcases H o with ⟨b, h, l⟩
      refine' l (lt_succ.2 _)
      rw [←
        show g (f.symm ⟨b, h⟩) = b by
          dsimp [g] <;> simp ]
      apply le_sup)

theorem sup_lt_ord {ι} (f : ι → Ordinal) {c : Ordinal} (H1 : # ι < c.cof) (H2 : ∀ i, f i < c) : sup.{u, u} f < c := by
  apply lt_of_le_of_neₓ
  ·
    rw [sup_le]
    exact fun i => le_of_ltₓ (H2 i)
  rintro h
  apply not_le_of_lt H1
  simpa [sup_ord, H2, h] using cof_sup_le.{u} f

theorem sup_lt {ι} (f : ι → Cardinal) {c : Cardinal} (H1 : # ι < c.ord.cof) (H2 : ∀ i, f i < c) :
    Cardinal.sup.{u, u} f < c := by
  rw [← ord_lt_ord, ← sup_ord]
  apply sup_lt_ord _ H1
  intro i
  rw [ord_lt_ord]
  apply H2

/--  If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : IsWellOrder α r] {s : Set (Set α)}
    (h₁ : Unbounded r $ ⋃₀s) (h₂ : # s < StrictOrder.cof r) : ∃ x ∈ s, Unbounded r x := by
  by_contra h
  simp only [not_exists, exists_prop, not_and, not_unbounded_iff] at h
  apply not_le_of_lt h₂
  let f : s → α := fun x : s => wo.wf.sup x (h x.1 x.2)
  let t : Set α := range f
  have : # t ≤ # s
  exact mk_range_le
  refine' le_transₓ _ this
  have : Unbounded r t := by
    intro x
    rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩
    refine' ⟨f ⟨c, hc⟩, mem_range_self _, _⟩
    intro hxz
    apply hxy
    refine' trans (wo.wf.lt_sup _ hy) hxz
  exact Cardinal.min_le _ (Subtype.mk t this)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If the union of s is unbounded and s is smaller than the cofinality,\n  then s has an unbounded member -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `unbounded_of_unbounded_Union [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α `β] [":" (Term.type "Type" [`u])] "}")
    (Term.explicitBinder "(" [`r] [":" (Term.arrow `α "→" (Term.arrow `α "→" (Term.prop "Prop")))] [] ")")
    (Term.instBinder "[" [`wo ":"] (Term.app `IsWellOrder [`α `r]) "]")
    (Term.explicitBinder "(" [`s] [":" (Term.arrow `β "→" (Term.app `Set [`α]))] [] ")")
    (Term.explicitBinder
     "("
     [`h₁]
     [":"
      («term_$__»
       (Term.app `Unbounded [`r])
       "$"
       (Set.Data.Set.Lattice.«term⋃_,_»
        "⋃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        ", "
        (Term.app `s [`x])))]
     []
     ")")
    (Term.explicitBinder
     "("
     [`h₂]
     [":" («term_<_» (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`β]) "<" (Term.app `StrictOrder.cof [`r]))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `β]))
     ","
     (Term.app `Unbounded [`r (Term.app `s [`x])]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `sUnion_range)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_»
              (Term.app
               (Cardinal.SetTheory.Cardinal.«term#» "#")
               [(Term.app
                 `range
                 [(Term.fun
                   "fun"
                   (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" `β)])] "=>" (Term.app `s [`i])))])])
              "<"
              (Term.app `StrictOrder.cof [`r])))]
           ":="
           (Term.app `lt_of_le_of_ltₓ [`mk_range_le `h₂]))))
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `unbounded_of_unbounded_sUnion [`r `h₁ `this]))]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
            ","
            (Tactic.rcasesPatLo
             (Tactic.rcasesPatMed
              [(Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                "⟩")])
             [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `u)]) [])]
           "⟩")])
        [])
       (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`x "," `u] "⟩")) [])])))
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
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `sUnion_range)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_<_»
             (Term.app
              (Cardinal.SetTheory.Cardinal.«term#» "#")
              [(Term.app
                `range
                [(Term.fun
                  "fun"
                  (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" `β)])] "=>" (Term.app `s [`i])))])])
             "<"
             (Term.app `StrictOrder.cof [`r])))]
          ":="
          (Term.app `lt_of_le_of_ltₓ [`mk_range_le `h₂]))))
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `unbounded_of_unbounded_sUnion [`r `h₁ `this]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
           ","
           (Tactic.rcasesPatLo
            (Tactic.rcasesPatMed
             [(Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
               "⟩")])
            [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `u)]) [])]
          "⟩")])
       [])
      (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`x "," `u] "⟩")) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`x "," `u] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`x "," `u] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] (Term.app `unbounded_of_unbounded_sUnion [`r `h₁ `this]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
      ","
      (Tactic.rcasesPatLo
       (Tactic.rcasesPatMed
        [(Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
          "⟩")])
       [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `u)]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `unbounded_of_unbounded_sUnion [`r `h₁ `this])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `unbounded_of_unbounded_sUnion
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
     []
     [(Term.typeSpec
       ":"
       («term_<_»
        (Term.app
         (Cardinal.SetTheory.Cardinal.«term#» "#")
         [(Term.app
           `range
           [(Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" `β)])] "=>" (Term.app `s [`i])))])])
        "<"
        (Term.app `StrictOrder.cof [`r])))]
     ":="
     (Term.app `lt_of_le_of_ltₓ [`mk_range_le `h₂]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `lt_of_le_of_ltₓ [`mk_range_le `h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mk_range_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_of_le_of_ltₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_»
   (Term.app
    (Cardinal.SetTheory.Cardinal.«term#» "#")
    [(Term.app
      `range
      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" `β)])] "=>" (Term.app `s [`i])))])])
   "<"
   (Term.app `StrictOrder.cof [`r]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `StrictOrder.cof [`r])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `StrictOrder.cof
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   (Cardinal.SetTheory.Cardinal.«term#» "#")
   [(Term.app
     `range
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" `β)])] "=>" (Term.app `s [`i])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `range
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" `β)])] "=>" (Term.app `s [`i])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" `β)])] "=>" (Term.app `s [`i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `s [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `range
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" `β)])] "=>" (Term.app `s [`i])))])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Cardinal.SetTheory.Cardinal.«term#» "#")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.«term#»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `sUnion_range)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sUnion_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] [":" `β]))
   ","
   (Term.app `Unbounded [`r (Term.app `s [`x])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Unbounded [`r (Term.app `s [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `s [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `s [`x]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Unbounded
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`β]) "<" (Term.app `StrictOrder.cof [`r]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `StrictOrder.cof [`r])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `StrictOrder.cof
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`β])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Cardinal.SetTheory.Cardinal.«term#» "#")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.«term#»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `Unbounded [`r])
   "$"
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    ", "
    (Term.app `s [`x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   ", "
   (Term.app `s [`x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `s [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
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
/--
    If the union of s is unbounded and s is smaller than the cofinality,
      then s has an unbounded member -/
  theorem
    unbounded_of_unbounded_Union
    { α β : Type u }
        ( r : α → α → Prop )
        [ wo : IsWellOrder α r ]
        ( s : β → Set α )
        ( h₁ : Unbounded r $ ⋃ x , s x )
        ( h₂ : # β < StrictOrder.cof r )
      : ∃ x : β , Unbounded r s x
    :=
      by
        rw [ ← sUnion_range ] at h₁
          have : # range fun i : β => s i < StrictOrder.cof r := lt_of_le_of_ltₓ mk_range_le h₂
          rcases unbounded_of_unbounded_sUnion r h₁ this with ⟨ _ , ⟨ x , rfl ⟩ , u ⟩
          exact ⟨ x , u ⟩

/--  The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ω ≤ # β) (h₂ : # α < (# β).ord.cof) :
    ∃ a : α, # (f ⁻¹' {a}) = # β := by
  have : ¬∀ a, # (f ⁻¹' {a}) < # β := by
    intro h
    apply not_lt_of_geₓ (ge_of_eq $ mk_univ)
    rw [← @preimage_univ _ _ f, ← Union_of_singleton, preimage_Union]
    apply lt_of_le_of_ltₓ mk_Union_le_sum_mk
    apply lt_of_le_of_ltₓ (sum_le_sup _)
    apply mul_lt_of_lt h₁ (lt_of_lt_of_leₓ h₂ $ cof_ord_le _)
    exact sup_lt _ h₂ h
  rw [not_forall] at this
  cases' this with x h
  use x
  apply le_antisymmₓ _ (le_of_not_gtₓ h)
  rw [le_mk_iff_exists_set]
  exact ⟨_, rfl⟩

/--  pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ # β) (h₁ : ω ≤ θ)
    (h₂ : # α < θ.ord.cof) : ∃ a : α, θ ≤ # (f ⁻¹' {a}) := by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  cases' infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂ with a ha
  use a
  rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  apply mk_preimage_of_injective _ _ Subtype.val_injective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `infinite_pigeonhole_set [])
  (Command.declSig
   [(Term.implicitBinder "{" [`β `α] [":" (Term.type "Type" [`u])] "}")
    (Term.implicitBinder "{" [`s] [":" (Term.app `Set [`β])] "}")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `s "→" `α)] [] ")")
    (Term.explicitBinder "(" [`θ] [":" `Cardinal] [] ")")
    (Term.explicitBinder
     "("
     [`hθ]
     [":" («term_≤_» `θ "≤" (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`s]))]
     []
     ")")
    (Term.explicitBinder "(" [`h₁] [":" («term_≤_» (Ordinal.SetTheory.Ordinal.termω "ω") "≤" `θ)] [] ")")
    (Term.explicitBinder
     "("
     [`h₂]
     [":" («term_<_» (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`α]) "<" `θ.ord.cof)]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" `α ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `t)] ":" (Term.app `Set [`β]) ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `h)] ":" (Init.Core.«term_⊆_» `t " ⊆ " `s) ")")])
     ","
     («term_∧_»
      («term_≤_» `θ "≤" (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`t]))
      "∧"
      (Term.forall
       "∀"
       [(Term.strictImplicitBinder "⦃" [`x] [] "⦄")
        (Term.simpleBinder [`hx] [(Term.typeSpec ":" (Init.Core.«term_∈_» `x " ∈ " `t))])]
       ","
       («term_=_» (Term.app `f [(Term.anonymousCtor "⟨" [`x "," (Term.app `h [`hx])] "⟩")]) "=" `a))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] (Term.app `infinite_pigeonhole_card [`f `θ `hθ `h₁ `h₂]))]
         []
         ["with" [(Lean.binderIdent `a) (Lean.binderIdent `ha)]])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [`a
           ","
           (Set.«term{_|_}»
            "{"
            `x
            "|"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] [":" (Init.Core.«term_∈_» `x " ∈ " `s)]))
             ","
             («term_=_» (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")]) "=" `a))
            "}")
           ","
           (Term.hole "_")
           ","
           (Term.hole "_")
           ","
           (Term.hole "_")]
          "⟩"))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rintro
              "rintro"
              [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
               (Tactic.rintroPat.one
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx')]) [])]
                 "⟩"))]
              [])
             [])
            (group (Tactic.exact "exact" `hx) [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.refine' "refine'" (Term.app `le_transₓ [`ha (Term.hole "_")])) [])
            (group (Tactic.apply "apply" `ge_of_eq) [])
            (group (Tactic.apply "apply" `Quotientₓ.sound) [])
            (group (Tactic.constructor "constructor") [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               `Equivₓ.trans
               [(Term.hole "_")
                (Term.proj
                 (Term.app `Equivₓ.subtypeSubtypeEquivSubtypeExists [(Term.hole "_") (Term.hole "_")])
                 "."
                 `symm)]))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `set_coe_eq_subtype)
                ","
                (Tactic.simpLemma [] [] `mem_singleton_iff)
                ","
                (Tactic.simpLemma [] [] `mem_preimage)
                ","
                (Tactic.simpLemma [] [] `mem_set_of_eq)]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
          (Tactic.rintroPat.one
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx')]) [])]
            "⟩"))]
         [])
        [])
       (group (Tactic.exact "exact" `hx') [])])))
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
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `infinite_pigeonhole_card [`f `θ `hθ `h₁ `h₂]))]
        []
        ["with" [(Lean.binderIdent `a) (Lean.binderIdent `ha)]])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`a
          ","
          (Set.«term{_|_}»
           "{"
           `x
           "|"
           («term∃_,_»
            "∃"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] [":" (Init.Core.«term_∈_» `x " ∈ " `s)]))
            ","
            («term_=_» (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")]) "=" `a))
           "}")
          ","
          (Term.hole "_")
          ","
          (Term.hole "_")
          ","
          (Term.hole "_")]
         "⟩"))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
              (Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx')]) [])]
                "⟩"))]
             [])
            [])
           (group (Tactic.exact "exact" `hx) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.refine' "refine'" (Term.app `le_transₓ [`ha (Term.hole "_")])) [])
           (group (Tactic.apply "apply" `ge_of_eq) [])
           (group (Tactic.apply "apply" `Quotientₓ.sound) [])
           (group (Tactic.constructor "constructor") [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `Equivₓ.trans
              [(Term.hole "_")
               (Term.proj
                (Term.app `Equivₓ.subtypeSubtypeEquivSubtypeExists [(Term.hole "_") (Term.hole "_")])
                "."
                `symm)]))
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `set_coe_eq_subtype)
               ","
               (Tactic.simpLemma [] [] `mem_singleton_iff)
               ","
               (Tactic.simpLemma [] [] `mem_preimage)
               ","
               (Tactic.simpLemma [] [] `mem_set_of_eq)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
         (Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx')]) [])]
           "⟩"))]
        [])
       [])
      (group (Tactic.exact "exact" `hx') [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `hx')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
    (Tactic.rintroPat.one
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx')]) [])]
      "⟩"))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.refine' "refine'" (Term.app `le_transₓ [`ha (Term.hole "_")])) [])
      (group (Tactic.apply "apply" `ge_of_eq) [])
      (group (Tactic.apply "apply" `Quotientₓ.sound) [])
      (group (Tactic.constructor "constructor") [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `Equivₓ.trans
         [(Term.hole "_")
          (Term.proj (Term.app `Equivₓ.subtypeSubtypeEquivSubtypeExists [(Term.hole "_") (Term.hole "_")]) "." `symm)]))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `set_coe_eq_subtype)
          ","
          (Tactic.simpLemma [] [] `mem_singleton_iff)
          ","
          (Tactic.simpLemma [] [] `mem_preimage)
          ","
          (Tactic.simpLemma [] [] `mem_set_of_eq)]
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
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `set_coe_eq_subtype)
     ","
     (Tactic.simpLemma [] [] `mem_singleton_iff)
     ","
     (Tactic.simpLemma [] [] `mem_preimage)
     ","
     (Tactic.simpLemma [] [] `mem_set_of_eq)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_preimage
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_singleton_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `set_coe_eq_subtype
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `Equivₓ.trans
    [(Term.hole "_")
     (Term.proj (Term.app `Equivₓ.subtypeSubtypeEquivSubtypeExists [(Term.hole "_") (Term.hole "_")]) "." `symm)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Equivₓ.trans
   [(Term.hole "_")
    (Term.proj (Term.app `Equivₓ.subtypeSubtypeEquivSubtypeExists [(Term.hole "_") (Term.hole "_")]) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `Equivₓ.subtypeSubtypeEquivSubtypeExists [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Equivₓ.subtypeSubtypeEquivSubtypeExists [(Term.hole "_") (Term.hole "_")])
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
  `Equivₓ.subtypeSubtypeEquivSubtypeExists
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Equivₓ.subtypeSubtypeEquivSubtypeExists [(Term.hole "_") (Term.hole "_")]) []]
 ")")
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
  `Equivₓ.trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.constructor', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.apply "apply" `Quotientₓ.sound)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Quotientₓ.sound
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `ge_of_eq)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ge_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine' "refine'" (Term.app `le_transₓ [`ha (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_transₓ [`ha (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `ha
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_transₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
         (Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx')]) [])]
           "⟩"))]
        [])
       [])
      (group (Tactic.exact "exact" `hx) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `hx)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
    (Tactic.rintroPat.one
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx')]) [])]
      "⟩"))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [`a
     ","
     (Set.«term{_|_}»
      "{"
      `x
      "|"
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] [":" (Init.Core.«term_∈_» `x " ∈ " `s)]))
       ","
       («term_=_» (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")]) "=" `a))
      "}")
     ","
     (Term.hole "_")
     ","
     (Term.hole "_")
     ","
     (Term.hole "_")]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`a
    ","
    (Set.«term{_|_}»
     "{"
     `x
     "|"
     («term∃_,_»
      "∃"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] [":" (Init.Core.«term_∈_» `x " ∈ " `s)]))
      ","
      («term_=_» (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")]) "=" `a))
     "}")
    ","
    (Term.hole "_")
    ","
    (Term.hole "_")
    ","
    (Term.hole "_")]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `x
   "|"
   («term∃_,_»
    "∃"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] [":" (Init.Core.«term_∈_» `x " ∈ " `s)]))
    ","
    («term_=_» (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")]) "=" `a))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `h)] [":" (Init.Core.«term_∈_» `x " ∈ " `s)]))
   ","
   («term_=_» (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")]) "=" `a))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")]) "=" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `f [(Term.anonymousCtor "⟨" [`x "," `h] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`x "," `h] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» `x " ∈ " `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
  infinite_pigeonhole_set
  { β α : Type u } { s : Set β } ( f : s → α ) ( θ : Cardinal ) ( hθ : θ ≤ # s ) ( h₁ : ω ≤ θ ) ( h₂ : # α < θ.ord.cof )
    : ∃ ( a : α ) ( t : Set β ) ( h : t ⊆ s ) , θ ≤ # t ∧ ∀ ⦃ x ⦄ hx : x ∈ t , f ⟨ x , h hx ⟩ = a
  :=
    by
      cases' infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha
        refine' ⟨ a , { x | ∃ h : x ∈ s , f ⟨ x , h ⟩ = a } , _ , _ , _ ⟩
        · rintro x ⟨ hx , hx' ⟩ exact hx
        ·
          refine' le_transₓ ha _
            apply ge_of_eq
            apply Quotientₓ.sound
            constructor
            refine' Equivₓ.trans _ Equivₓ.subtypeSubtypeEquivSubtypeExists _ _ . symm
            simp only [ set_coe_eq_subtype , mem_singleton_iff , mem_preimage , mem_set_of_eq ]
        rintro x ⟨ hx , hx' ⟩
        exact hx'

end Ordinal

namespace Cardinal

open Ordinal

local infixr:0 "^" => @pow Cardinal.{u} Cardinal Cardinal.hasPow

/--  A cardinal is a limit if it is not zero or a successor
  cardinal. Note that `ω` is a limit cardinal by this definition. -/
def is_limit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀, ∀ x < c, ∀, succ x < c

/--  A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ω` is a strong limit by this definition. -/
def is_strong_limit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀, ∀ x < c, ∀, (2^x) < c

theorem is_strong_limit.is_limit {c} (H : is_strong_limit c) : is_limit c :=
  ⟨H.1, fun x h => lt_of_le_of_ltₓ (succ_le.2 $ cantor _) (H.2 _ h)⟩

/--  A cardinal is regular if it is infinite and it equals its own cofinality. -/
def IsRegular (c : Cardinal) : Prop :=
  ω ≤ c ∧ c.ord.cof = c

theorem is_regular.pos {c : Cardinal} (H : c.is_regular) : 0 < c :=
  omega_pos.trans_le H.left

theorem is_regular.ord_pos {c : Cardinal} (H : c.is_regular) : 0 < c.ord := by
  rw [Cardinal.lt_ord]
  exact H.pos

theorem cof_is_regular {o : Ordinal} (h : o.is_limit) : IsRegular o.cof :=
  ⟨omega_le_cof.2 h, cof_cof _⟩

theorem omega_is_regular : IsRegular ω :=
  ⟨le_reflₓ _, by
    simp ⟩

theorem succ_is_regular {c : Cardinal.{u}} (h : ω ≤ c) : IsRegular (succ c) :=
  ⟨le_transₓ h (le_of_ltₓ $ lt_succ_self _), by
    refine' le_antisymmₓ (cof_ord_le _) (succ_le.2 _)
    cases' Quotientₓ.exists_rep (succ c) with α αe
    simp at αe
    rcases ord_eq α with ⟨r, wo, re⟩
    skip
    have := ord_is_limit (le_transₓ h $ le_of_ltₓ $ lt_succ_self _)
    rw [← αe, re] at this⊢
    rcases cof_eq' r this with ⟨S, H, Se⟩
    rw [← Se]
    apply lt_imp_lt_of_le_imp_le fun h : # S ≤ c => mul_le_mul_right' h c
    rw [mul_eq_self h, ← succ_le, ← αe, ← sum_const']
    refine' le_transₓ _ (sum_le_sum (fun x : S => card (typein r x)) _ _)
    ·
      simp only [← card_typein, ← mk_sigma]
      refine' ⟨embedding.of_surjective _ _⟩
      ·
        exact fun x => x.2.1
      ·
        exact fun a =>
          let ⟨b, h, ab⟩ := H a
          ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩
    ·
      intro i
      rw [← lt_succ, ← lt_ord, ← αe, re]
      apply typein_lt_type⟩

/-- 
A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (w : # α < # β) (w' : ω ≤ # α) :
    ∃ a : α, # α < # (f ⁻¹' {a}) := by
  simp_rw [← succ_le]
  exact
    Ordinal.infinite_pigeonhole_card f (# α).succ (succ_le.mpr w) (w'.trans (lt_succ_self _).le)
      ((lt_succ_self _).trans_le (succ_is_regular w').2.Ge)

/-- 
A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type _} (f : β → α) (w : # α < # β) (w' : _root_.infinite α) :
    ∃ a : α, _root_.infinite (f ⁻¹' {a}) := by
  simp_rw [Cardinal.infinite_iff]  at w'⊢
  cases' infinite_pigeonhole_card_lt f w w' with a ha
  exact ⟨a, w'.trans ha.le⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIf an infinite type `β` can be expressed as a union of finite sets,\nthen the cardinality of the collection of those finite sets\nmust be at least the cardinality of `β`.\n-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `le_range_of_union_finset_eq_top [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α `β] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `Infinite [`β]) "]")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `α "→" (Term.app `Finset [`β]))] [] ")")
    (Term.explicitBinder
     "("
     [`w]
     [":"
      («term_=_»
       (Set.Data.Set.Lattice.«term⋃_,_»
        "⋃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
        ", "
        (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Term.app `Set [`β]))]] ")"))
       "="
       (Order.BoundedOrder.«term⊤» "⊤"))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`β])
     "≤"
     (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [(Term.app `range [`f])]))))
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
           [`k []]
           [(Term.typeSpec ":" (Term.app `_root_.infinite [(Term.app `range [`f])]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `infinite_coe_iff)] "]") []) [])
               (group (Tactic.apply "apply" (Term.app `mt [(Term.app `union_finset_finite_of_range_finite [`f])])) [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `w)] "]") []) [])
               (group (Tactic.exact "exact" `infinite_univ) [])]))))))
        [])
       (group (byContra "by_contra" [`h]) [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `not_leₓ)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `u
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`b] [])]
              ","
              («term∃_,_»
               "∃"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
               ","
               (Init.Core.«term_∈_» `b " ∈ " (Term.app `f [`a])))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`b] [])]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simpa
                   "simpa"
                   []
                   []
                   []
                   []
                   ["using"
                    (Term.app
                     (Term.paren "(" [`w.ge [(Term.typeAscription ":" (Term.hole "_"))]] ")")
                     [(Term.app `Set.mem_univ [`b])])])
                  [])]))))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `u'
           [(Term.typeSpec ":" (Term.arrow `β "→" (Term.app `range [`f])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`b] [])]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `f [(Term.proj (Term.app `u [`b]) "." `some)])
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
              "⟩"))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`v' []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`a] [])]
              ","
              («term_≤_»
               (Set.Data.Set.Basic.«term_⁻¹'_»
                `u'
                " ⁻¹' "
                (Set.«term{_}»
                 "{"
                 [(Term.anonymousCtor
                   "⟨"
                   [(Term.app `f [`a])
                    ","
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                   "⟩")]
                 "}"))
               "≤"
               (Term.app `f [`a]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one (Tactic.rcasesPat.one `a))
                  (Tactic.rintroPat.one (Tactic.rcasesPat.one `p))
                  (Tactic.rintroPat.one (Tactic.rcasesPat.one `m))]
                 [])
                [])
               (group (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`m] []))]) [])
               (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `m)] "]") []) [])
               (group
                (Tactic.apply
                 "apply"
                 (Term.fun
                  "fun"
                  (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" (Term.proj (Term.app `u [`b]) "." `some_spec))))
                [])]))))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo
               (Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                   ","
                   (Tactic.rcasesPatLo
                    (Tactic.rcasesPatMed
                     [(Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                       "⟩")])
                    [])]
                  "⟩")])
               [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `p)]) [])]
             "⟩")])]
         []
         [":=" [(Term.app `exists_infinite_fiber [`u' `h `k])]])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           (Term.explicit "@" `Infinite.of_injective)
           [(Term.hole "_")
            (Term.hole "_")
            `p
            (Term.app `inclusion [(Term.app `v' [`a])])
            (Term.app `inclusion_injective [(Term.hole "_")])])
          "."
          `False))
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`k []]
          [(Term.typeSpec ":" (Term.app `_root_.infinite [(Term.app `range [`f])]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `infinite_coe_iff)] "]") []) [])
              (group (Tactic.apply "apply" (Term.app `mt [(Term.app `union_finset_finite_of_range_finite [`f])])) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `w)] "]") []) [])
              (group (Tactic.exact "exact" `infinite_univ) [])]))))))
       [])
      (group (byContra "by_contra" [`h]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `not_leₓ)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `u
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`b] [])]
             ","
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
              ","
              (Init.Core.«term_∈_» `b " ∈ " (Term.app `f [`a])))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`b] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simpa
                  "simpa"
                  []
                  []
                  []
                  []
                  ["using"
                   (Term.app
                    (Term.paren "(" [`w.ge [(Term.typeAscription ":" (Term.hole "_"))]] ")")
                    [(Term.app `Set.mem_univ [`b])])])
                 [])]))))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `u'
          [(Term.typeSpec ":" (Term.arrow `β "→" (Term.app `range [`f])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`b] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app `f [(Term.proj (Term.app `u [`b]) "." `some)])
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
             "⟩"))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`v' []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`a] [])]
             ","
             («term_≤_»
              (Set.Data.Set.Basic.«term_⁻¹'_»
               `u'
               " ⁻¹' "
               (Set.«term{_}»
                "{"
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app `f [`a])
                   ","
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
                  "⟩")]
                "}"))
              "≤"
              (Term.app `f [`a]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `a))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `p))
                 (Tactic.rintroPat.one (Tactic.rcasesPat.one `m))]
                [])
               [])
              (group (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`m] []))]) [])
              (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `m)] "]") []) [])
              (group
               (Tactic.apply
                "apply"
                (Term.fun
                 "fun"
                 (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" (Term.proj (Term.app `u [`b]) "." `some_spec))))
               [])]))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo
              (Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
                  ","
                  (Tactic.rcasesPatLo
                   (Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                      "⟩")])
                   [])]
                 "⟩")])
              [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `p)]) [])]
            "⟩")])]
        []
        [":=" [(Term.app `exists_infinite_fiber [`u' `h `k])]])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.proj
         (Term.app
          (Term.explicit "@" `Infinite.of_injective)
          [(Term.hole "_")
           (Term.hole "_")
           `p
           (Term.app `inclusion [(Term.app `v' [`a])])
           (Term.app `inclusion_injective [(Term.hole "_")])])
         "."
         `False))
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
   (Term.proj
    (Term.app
     (Term.explicit "@" `Infinite.of_injective)
     [(Term.hole "_")
      (Term.hole "_")
      `p
      (Term.app `inclusion [(Term.app `v' [`a])])
      (Term.app `inclusion_injective [(Term.hole "_")])])
    "."
    `False))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    (Term.explicit "@" `Infinite.of_injective)
    [(Term.hole "_")
     (Term.hole "_")
     `p
     (Term.app `inclusion [(Term.app `v' [`a])])
     (Term.app `inclusion_injective [(Term.hole "_")])])
   "."
   `False)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.explicit "@" `Infinite.of_injective)
   [(Term.hole "_")
    (Term.hole "_")
    `p
    (Term.app `inclusion [(Term.app `v' [`a])])
    (Term.app `inclusion_injective [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `inclusion_injective [(Term.hole "_")])
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
  `inclusion_injective
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `inclusion_injective [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `inclusion [(Term.app `v' [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `v' [`a])
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
  `v'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `v' [`a]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `inclusion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `inclusion [(Term.paren "(" [(Term.app `v' [`a]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `Infinite.of_injective)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Infinite.of_injective
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.explicit "@" `Infinite.of_injective)
   [(Term.hole "_")
    (Term.hole "_")
    `p
    (Term.paren "(" [(Term.app `inclusion [(Term.paren "(" [(Term.app `v' [`a]) []] ")")]) []] ")")
    (Term.paren "(" [(Term.app `inclusion_injective [(Term.hole "_")]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo
         (Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                 "⟩")])
              [])]
            "⟩")])
         [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `p)]) [])]
       "⟩")])]
   []
   [":=" [(Term.app `exists_infinite_fiber [`u' `h `k])]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `exists_infinite_fiber [`u' `h `k])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `u'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exists_infinite_fiber
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatMed', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.clear', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.clear', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`v' []]
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`a] [])]
        ","
        («term_≤_»
         (Set.Data.Set.Basic.«term_⁻¹'_»
          `u'
          " ⁻¹' "
          (Set.«term{_}»
           "{"
           [(Term.anonymousCtor
             "⟨"
             [(Term.app `f [`a])
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
             "⟩")]
           "}"))
         "≤"
         (Term.app `f [`a]))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rintro
           "rintro"
           [(Tactic.rintroPat.one (Tactic.rcasesPat.one `a))
            (Tactic.rintroPat.one (Tactic.rcasesPat.one `p))
            (Tactic.rintroPat.one (Tactic.rcasesPat.one `m))]
           [])
          [])
         (group (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`m] []))]) [])
         (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `m)] "]") []) [])
         (group
          (Tactic.apply
           "apply"
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" (Term.proj (Term.app `u [`b]) "." `some_spec))))
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
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.one `a))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `p))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `m))]
        [])
       [])
      (group (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`m] []))]) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `m)] "]") []) [])
      (group
       (Tactic.apply
        "apply"
        (Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" (Term.proj (Term.app `u [`b]) "." `some_spec))))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply
   "apply"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" (Term.proj (Term.app `u [`b]) "." `some_spec))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`b] [])] "=>" (Term.proj (Term.app `u [`b]) "." `some_spec)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `u [`b]) "." `some_spec)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `u [`b])
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
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `u [`b]) []] ")")
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `m)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`m] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one (Tactic.rcasesPat.one `a))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `p))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `m))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`a] [])]
   ","
   («term_≤_»
    (Set.Data.Set.Basic.«term_⁻¹'_»
     `u'
     " ⁻¹' "
     (Set.«term{_}»
      "{"
      [(Term.anonymousCtor
        "⟨"
        [(Term.app `f [`a])
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
        "⟩")]
      "}"))
    "≤"
    (Term.app `f [`a])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Set.Data.Set.Basic.«term_⁻¹'_»
    `u'
    " ⁻¹' "
    (Set.«term{_}»
     "{"
     [(Term.anonymousCtor
       "⟨"
       [(Term.app `f [`a])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
       "⟩")]
     "}"))
   "≤"
   (Term.app `f [`a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`a])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Set.Data.Set.Basic.«term_⁻¹'_»
   `u'
   " ⁻¹' "
   (Set.«term{_}»
    "{"
    [(Term.anonymousCtor
      "⟨"
      [(Term.app `f [`a])
       ","
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
      "⟩")]
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Basic.«term_⁻¹'_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_}»
   "{"
   [(Term.anonymousCtor
     "⟨"
     [(Term.app `f [`a])
      ","
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
     "⟩")]
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `f [`a])
    ","
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`a])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `u'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 81, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `u'
     [(Term.typeSpec ":" (Term.arrow `β "→" (Term.app `range [`f])))]
     ":="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`b] [])]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `f [(Term.proj (Term.app `u [`b]) "." `some)])
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
        "⟩"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`b] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [(Term.app `f [(Term.proj (Term.app `u [`b]) "." `some)])
      ","
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `f [(Term.proj (Term.app `u [`b]) "." `some)])
    ","
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [(Term.proj (Term.app `u [`b]) "." `some)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `u [`b]) "." `some)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `u [`b])
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
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `u [`b]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow `β "→" (Term.app `range [`f]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `u
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`b] [])]
        ","
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
         ","
         (Init.Core.«term_∈_» `b " ∈ " (Term.app `f [`a])))))]
     ":="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`b] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simpa
             "simpa"
             []
             []
             []
             []
             ["using"
              (Term.app
               (Term.paren "(" [`w.ge [(Term.typeAscription ":" (Term.hole "_"))]] ")")
               [(Term.app `Set.mem_univ [`b])])])
            [])]))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`b] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.simpa
          "simpa"
          []
          []
          []
          []
          ["using"
           (Term.app
            (Term.paren "(" [`w.ge [(Term.typeAscription ":" (Term.hole "_"))]] ")")
            [(Term.app `Set.mem_univ [`b])])])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpa
        "simpa"
        []
        []
        []
        []
        ["using"
         (Term.app
          (Term.paren "(" [`w.ge [(Term.typeAscription ":" (Term.hole "_"))]] ")")
          [(Term.app `Set.mem_univ [`b])])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   []
   []
   []
   ["using"
    (Term.app
     (Term.paren "(" [`w.ge [(Term.typeAscription ":" (Term.hole "_"))]] ")")
     [(Term.app `Set.mem_univ [`b])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.paren "(" [`w.ge [(Term.typeAscription ":" (Term.hole "_"))]] ")") [(Term.app `Set.mem_univ [`b])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set.mem_univ [`b])
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
  `Set.mem_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Set.mem_univ [`b]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.paren "(" [`w.ge [(Term.typeAscription ":" (Term.hole "_"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `w.ge
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`b] [])]
   ","
   («term∃_,_»
    "∃"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
    ","
    (Init.Core.«term_∈_» `b " ∈ " (Term.app `f [`a]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term∃_,_»
   "∃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   ","
   (Init.Core.«term_∈_» `b " ∈ " (Term.app `f [`a])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term∃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_» `b " ∈ " (Term.app `f [`a]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`a])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `not_leₓ)] "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `not_leₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (byContra "by_contra" [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'byContra', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`k []]
     [(Term.typeSpec ":" (Term.app `_root_.infinite [(Term.app `range [`f])]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `infinite_coe_iff)] "]") []) [])
         (group (Tactic.apply "apply" (Term.app `mt [(Term.app `union_finset_finite_of_range_finite [`f])])) [])
         (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `w)] "]") []) [])
         (group (Tactic.exact "exact" `infinite_univ) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `infinite_coe_iff)] "]") []) [])
      (group (Tactic.apply "apply" (Term.app `mt [(Term.app `union_finset_finite_of_range_finite [`f])])) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `w)] "]") []) [])
      (group (Tactic.exact "exact" `infinite_univ) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `infinite_univ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `infinite_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `w)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.app `mt [(Term.app `union_finset_finite_of_range_finite [`f])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mt [(Term.app `union_finset_finite_of_range_finite [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `union_finset_finite_of_range_finite [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `union_finset_finite_of_range_finite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `union_finset_finite_of_range_finite [`f]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `infinite_coe_iff)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `infinite_coe_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `_root_.infinite [(Term.app `range [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `range [`f]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `_root_.infinite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_≤_»
   (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`β])
   "≤"
   (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [(Term.app `range [`f])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [(Term.app `range [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `range [`f]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Cardinal.SetTheory.Cardinal.«term#» "#")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.«term#»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app (Cardinal.SetTheory.Cardinal.«term#» "#") [`β])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Cardinal.SetTheory.Cardinal.«term#» "#")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.«term#»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
    ", "
    (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Term.app `Set [`β]))]] ")"))
   "="
   (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊤»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   ", "
   (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Term.app `Set [`β]))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(Term.app `f [`a]) [(Term.typeAscription ":" (Term.app `Set [`β]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [`β])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `f [`a])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
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
/--
    If an infinite type `β` can be expressed as a union of finite sets,
    then the cardinality of the collection of those finite sets
    must be at least the cardinality of `β`.
    -/
  theorem
    le_range_of_union_finset_eq_top
    { α β : Type _ } [ Infinite β ] ( f : α → Finset β ) ( w : ⋃ a , ( f a : Set β ) = ⊤ ) : # β ≤ # range f
    :=
      by
        have
            k
              : _root_.infinite range f
              :=
              by rw [ infinite_coe_iff ] apply mt union_finset_finite_of_range_finite f rw [ w ] exact infinite_univ
          by_contra h
          simp only [ not_leₓ ] at h
          let u : ∀ b , ∃ a , b ∈ f a := fun b => by simpa using ( w.ge : _ ) Set.mem_univ b
          let u' : β → range f := fun b => ⟨ f u b . some , by simp ⟩
          have
            v'
              : ∀ a , u' ⁻¹' { ⟨ f a , by simp ⟩ } ≤ f a
              :=
              by rintro a p m simp at m rw [ ← m ] apply fun b => u b . some_spec
          obtain ⟨ ⟨ - , ⟨ a , rfl ⟩ ⟩ , p ⟩ := exists_infinite_fiber u' h k
          exact @ Infinite.of_injective _ _ p inclusion v' a inclusion_injective _ . False

theorem sup_lt_ord_of_is_regular {ι} (f : ι → Ordinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c.ord) :
    Ordinal.sup.{u, u} f < c.ord := by
  apply sup_lt_ord _ _ H2
  rw [hc.2]
  exact H1

theorem sup_lt_of_is_regular {ι} (f : ι → Cardinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c) :
    sup.{u, u} f < c := by
  apply sup_lt _ _ H2
  rwa [hc.2]

theorem sum_lt_of_is_regular {ι} (f : ι → Cardinal) {c} (hc : IsRegular c) (H1 : # ι < c) (H2 : ∀ i, f i < c) :
    Sum.{u, u} f < c :=
  lt_of_le_of_ltₓ (sum_le_sup _) $ mul_lt_of_lt hc.1 H1 $ sup_lt_of_is_regular f hc H1 H2

/--  A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def is_inaccessible (c : Cardinal) :=
  ω < c ∧ IsRegular c ∧ is_strong_limit c

theorem is_inaccessible.mk {c} (h₁ : ω < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀, ∀ x < c, ∀, (2^x) < c) : is_inaccessible c :=
  ⟨h₁, ⟨le_of_ltₓ h₁, le_antisymmₓ (cof_ord_le _) h₂⟩, ne_of_gtₓ (lt_transₓ omega_pos h₁), h₃⟩

theorem univ_inaccessible : is_inaccessible univ.{u, v} :=
  is_inaccessible.mk
    (by
      simpa using lift_lt_univ' ω)
    (by
      simp )
    fun c h => by
    rcases lt_univ'.1 h with ⟨c, rfl⟩
    rw [← lift_two_power.{u, max (u + 1) v}]
    apply lift_lt_univ'

theorem lt_power_cof {c : Cardinal.{u}} : ω ≤ c → c < (c^cof c.ord) :=
  Quotientₓ.induction_on c $ fun α h => by
    rcases ord_eq α with ⟨r, wo, re⟩
    skip
    have := ord_is_limit h
    rw [mk_def, re] at this⊢
    rcases cof_eq' r this with ⟨S, H, Se⟩
    have := sum_lt_prod (fun a : S => # { x // r x a }) (fun _ => # α) fun i => _
    ·
      simp only [Cardinal.prod_const, Cardinal.lift_id, ← Se, ← mk_sigma, power_def] at this⊢
      refine' lt_of_le_of_ltₓ _ this
      refine' ⟨embedding.of_surjective _ _⟩
      ·
        exact fun x => x.2.1
      ·
        exact fun a =>
          let ⟨b, h, ab⟩ := H a
          ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩
    ·
      have := typein_lt_type r i
      rwa [← re, lt_ord] at this

theorem lt_cof_power {a b : Cardinal} (ha : ω ≤ a) (b1 : 1 < b) : a < cof (b^a).ord := by
  have b0 : b ≠ 0 := ne_of_gtₓ (lt_transₓ zero_lt_one b1)
  apply lt_imp_lt_of_le_imp_le (power_le_power_left $ power_ne_zero a b0)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof (le_transₓ ha $ le_of_ltₓ $ cantor' _ b1)

end Cardinal

