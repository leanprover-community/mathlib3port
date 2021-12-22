import Mathbin.Data.SetLike.Fintype
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.PGroup

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

## Main definitions

* `sylow p G` : The type of Sylow `p`-subgroups of `G`.

## Main statements

* `exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `is_p_group.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `sylow_conjugate`: A generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modeq_one`: A generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/


open Fintype MulAction Subgroup

section InfiniteSylow

variable (p : ℕ) (G : Type _) [Groupₓ G]

/--  A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure Sylow extends Subgroup G where
  is_p_group' : IsPGroup p to_subgroup
  is_maximal' : ∀ {Q : Subgroup G}, IsPGroup p Q → to_subgroup ≤ Q → Q = to_subgroup

variable {p} {G}

namespace Sylow

instance : Coe (Sylow p G) (Subgroup G) :=
  ⟨Sylow.toSubgroup⟩

@[simp]
theorem to_subgroup_eq_coe {P : Sylow p G} : P.to_subgroup = ↑P :=
  rfl

@[ext]
theorem ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q := by
  cases P <;> cases Q <;> congr

theorem ext_iff {P Q : Sylow p G} : P = Q ↔ (P : Subgroup G) = Q :=
  ⟨congr_argₓ coeₓ, ext⟩

-- failed to format: format: uncaught backtrack exception
instance : SetLike ( Sylow p G ) G where coe := coeₓ coe_injective' P Q h := ext ( SetLike.coe_injective h )

end Sylow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " A generalization of **Sylow's first theorem**.\n  Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `IsPGroup.exists_le_sylow [])
  (Command.declSig
   [(Term.implicitBinder "{" [`P] [":" (Term.app `Subgroup [`G])] "}")
    (Term.explicitBinder "(" [`hP] [":" (Term.app `IsPGroup [`p `P])] [] ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `Q)] [":" (Term.app `Sylow [`p `G])]))
     ","
     («term_≤_» `P "≤" `Q))))
  (Command.declValSimple
   ":="
   (Term.app
    `Exists.elim
    [(Term.app
      `Zorn.zorn_nonempty_partial_order₀
      [(Set.«term{_|_}»
        "{"
        (Mathlib.ExtendedBinder.extBinder `Q [":" (Term.app `Subgroup [`G])])
        "|"
        (Term.app `IsPGroup [`p `Q])
        "}")
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`c `hc1 `hc2 `Q `hQ] [])]
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.structInst
            "{"
            []
            [(group
              (Term.structInstField
               (Term.structInstLVal `Carrier [])
               ":="
               (Set.Data.Set.Lattice.«term⋃_,_»
                "⋃"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `R)] [":" `c]))
                ", "
                `R))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `one_mem' [])
               ":="
               (Term.anonymousCtor
                "⟨"
                [`Q
                 ","
                 (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩") "," `rfl] "⟩")
                 ","
                 `Q.one_mem]
                "⟩"))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `inv_mem' [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`g] [])
                  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")]
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [`R
                   ","
                   (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
                   ","
                   (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])]
                  "⟩"))))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `mul_mem' [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`g `h] [])
                  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
                  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hh] "⟩")]
                 "=>"
                 (Term.app
                  (Term.proj
                   (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
                   "."
                   `elim)
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`T] [])]
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [`S
                       ","
                       (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
                       ","
                       (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
                      "⟩")))
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`T] [])]
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [`R
                       ","
                       (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
                       ","
                       (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
                      "⟩")))]))))
              [])]
            (Term.optEllipsis [])
            []
            "}")
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor
               "⟨"
               [`g "," (Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hg]
               "⟩")]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    `exists_imp_exists
                    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
                     (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])]))
                  [])
                 (group
                  (tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff) "," (Tactic.rwRule [] `coe_pow)] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hk] ["⊢"]))])
                  [])])))))
           ","
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`M `hM `g `hg] [])]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [`M "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`M "," `hM] "⟩") "," `rfl] "⟩") "," `hg]
              "⟩")))]
          "⟩")))
       `P
       `hP])
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`Q] []) (Term.anonymousCtor "⟨" [`hQ1 "," `hQ2 "," `hQ3] "⟩")]
       "=>"
       (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ1 "," `hQ3] "⟩") "," `hQ2] "⟩")))])
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
  (Term.app
   `Exists.elim
   [(Term.app
     `Zorn.zorn_nonempty_partial_order₀
     [(Set.«term{_|_}»
       "{"
       (Mathlib.ExtendedBinder.extBinder `Q [":" (Term.app `Subgroup [`G])])
       "|"
       (Term.app `IsPGroup [`p `Q])
       "}")
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`c `hc1 `hc2 `Q `hQ] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.structInst
           "{"
           []
           [(group
             (Term.structInstField
              (Term.structInstLVal `Carrier [])
              ":="
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `R)] [":" `c]))
               ", "
               `R))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `one_mem' [])
              ":="
              (Term.anonymousCtor
               "⟨"
               [`Q "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩") "," `rfl] "⟩") "," `Q.one_mem]
               "⟩"))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `inv_mem' [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`g] [])
                 (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")]
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [`R
                  ","
                  (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
                  ","
                  (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])]
                 "⟩"))))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `mul_mem' [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`g `h] [])
                 (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
                 (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hh] "⟩")]
                "=>"
                (Term.app
                 (Term.proj
                  (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
                  "."
                  `elim)
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`T] [])]
                    "=>"
                    (Term.anonymousCtor
                     "⟨"
                     [`S
                      ","
                      (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
                      ","
                      (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
                     "⟩")))
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`T] [])]
                    "=>"
                    (Term.anonymousCtor
                     "⟨"
                     [`R
                      ","
                      (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
                      ","
                      (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
                     "⟩")))]))))
             [])]
           (Term.optEllipsis [])
           []
           "}")
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.anonymousCtor
              "⟨"
              [`g "," (Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hg]
              "⟩")]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `exists_imp_exists
                   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
                    (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])]))
                 [])
                (group
                 (tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff) "," (Tactic.rwRule [] `coe_pow)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hk] ["⊢"]))])
                 [])])))))
          ","
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`M `hM `g `hg] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [`M "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`M "," `hM] "⟩") "," `rfl] "⟩") "," `hg]
             "⟩")))]
         "⟩")))
      `P
      `hP])
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`Q] []) (Term.anonymousCtor "⟨" [`hQ1 "," `hQ2 "," `hQ3] "⟩")]
      "=>"
      (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ1 "," `hQ3] "⟩") "," `hQ2] "⟩")))])
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
    [(Term.simpleBinder [`Q] []) (Term.anonymousCtor "⟨" [`hQ1 "," `hQ2 "," `hQ3] "⟩")]
    "=>"
    (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ1 "," `hQ3] "⟩") "," `hQ2] "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ1 "," `hQ3] "⟩") "," `hQ2] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hQ2
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`Q "," `hQ1 "," `hQ3] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hQ3
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hQ1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Q
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
  (Term.anonymousCtor "⟨" [`hQ1 "," `hQ2 "," `hQ3] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hQ3
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hQ2
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hQ1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app
   `Zorn.zorn_nonempty_partial_order₀
   [(Set.«term{_|_}»
     "{"
     (Mathlib.ExtendedBinder.extBinder `Q [":" (Term.app `Subgroup [`G])])
     "|"
     (Term.app `IsPGroup [`p `Q])
     "}")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`c `hc1 `hc2 `Q `hQ] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [(Term.structInst
         "{"
         []
         [(group
           (Term.structInstField
            (Term.structInstLVal `Carrier [])
            ":="
            (Set.Data.Set.Lattice.«term⋃_,_»
             "⋃"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `R)] [":" `c]))
             ", "
             `R))
           [","])
          (group
           (Term.structInstField
            (Term.structInstLVal `one_mem' [])
            ":="
            (Term.anonymousCtor
             "⟨"
             [`Q "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩") "," `rfl] "⟩") "," `Q.one_mem]
             "⟩"))
           [","])
          (group
           (Term.structInstField
            (Term.structInstLVal `inv_mem' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`g] [])
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")]
              "=>"
              (Term.anonymousCtor
               "⟨"
               [`R
                ","
                (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
                ","
                (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])]
               "⟩"))))
           [","])
          (group
           (Term.structInstField
            (Term.structInstLVal `mul_mem' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`g `h] [])
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hh] "⟩")]
              "=>"
              (Term.app
               (Term.proj
                (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
                "."
                `elim)
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`T] [])]
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [`S
                    ","
                    (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
                    ","
                    (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
                   "⟩")))
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`T] [])]
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [`R
                    ","
                    (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
                    ","
                    (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
                   "⟩")))]))))
           [])]
         (Term.optEllipsis [])
         []
         "}")
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`g "," (Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hg] "⟩")]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `exists_imp_exists
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
                  (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])]))
               [])
              (group
               (tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff) "," (Tactic.rwRule [] `coe_pow)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hk] ["⊢"]))])
               [])])))))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`M `hM `g `hg] [])]
          "=>"
          (Term.anonymousCtor
           "⟨"
           [`M "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`M "," `hM] "⟩") "," `rfl] "⟩") "," `hg]
           "⟩")))]
       "⟩")))
    `P
    `hP])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hP
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `P
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
    [(Term.simpleBinder [`c `hc1 `hc2 `Q `hQ] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [(Term.structInst
       "{"
       []
       [(group
         (Term.structInstField
          (Term.structInstLVal `Carrier [])
          ":="
          (Set.Data.Set.Lattice.«term⋃_,_»
           "⋃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `R)] [":" `c]))
           ", "
           `R))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `one_mem' [])
          ":="
          (Term.anonymousCtor
           "⟨"
           [`Q "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩") "," `rfl] "⟩") "," `Q.one_mem]
           "⟩"))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `inv_mem' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`g] [])
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [`R
              ","
              (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
              ","
              (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])]
             "⟩"))))
         [","])
        (group
         (Term.structInstField
          (Term.structInstLVal `mul_mem' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`g `h] [])
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
             (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hh] "⟩")]
            "=>"
            (Term.app
             (Term.proj
              (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
              "."
              `elim)
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`T] [])]
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [`S
                  ","
                  (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
                  ","
                  (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
                 "⟩")))
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`T] [])]
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [`R
                  ","
                  (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
                  ","
                  (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
                 "⟩")))]))))
         [])]
       (Term.optEllipsis [])
       []
       "}")
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`g "," (Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hg] "⟩")]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               `exists_imp_exists
               [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
                (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])]))
             [])
            (group
             (tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff) "," (Tactic.rwRule [] `coe_pow)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hk] ["⊢"]))])
             [])])))))
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`M `hM `g `hg] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [`M "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`M "," `hM] "⟩") "," `rfl] "⟩") "," `hg]
         "⟩")))]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.structInst
     "{"
     []
     [(group
       (Term.structInstField
        (Term.structInstLVal `Carrier [])
        ":="
        (Set.Data.Set.Lattice.«term⋃_,_»
         "⋃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `R)] [":" `c]))
         ", "
         `R))
       [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `one_mem' [])
        ":="
        (Term.anonymousCtor
         "⟨"
         [`Q "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩") "," `rfl] "⟩") "," `Q.one_mem]
         "⟩"))
       [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `inv_mem' [])
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`g] [])
           (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")]
          "=>"
          (Term.anonymousCtor
           "⟨"
           [`R
            ","
            (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
            ","
            (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])]
           "⟩"))))
       [","])
      (group
       (Term.structInstField
        (Term.structInstLVal `mul_mem' [])
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`g `h] [])
           (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
           (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hh] "⟩")]
          "=>"
          (Term.app
           (Term.proj
            (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
            "."
            `elim)
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`T] [])]
              "=>"
              (Term.anonymousCtor
               "⟨"
               [`S
                ","
                (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
                ","
                (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
               "⟩")))
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`T] [])]
              "=>"
              (Term.anonymousCtor
               "⟨"
               [`R
                ","
                (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
                ","
                (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
               "⟩")))]))))
       [])]
     (Term.optEllipsis [])
     []
     "}")
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.anonymousCtor "⟨" [`g "," (Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hg] "⟩")]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.refine'
            "refine'"
            (Term.app
             `exists_imp_exists
             [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
              (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])]))
           [])
          (group
           (tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff) "," (Tactic.rwRule [] `coe_pow)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hk] ["⊢"]))])
           [])])))))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`M `hM `g `hg] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [`M "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`M "," `hM] "⟩") "," `rfl] "⟩") "," `hg]
       "⟩")))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`M `hM `g `hg] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [`M "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`M "," `hM] "⟩") "," `rfl] "⟩") "," `hg]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`M "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`M "," `hM] "⟩") "," `rfl] "⟩") "," `hg]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`M "," `hM] "⟩") "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`M "," `hM] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hM
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.anonymousCtor "⟨" [`g "," (Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hg] "⟩")]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.refine'
          "refine'"
          (Term.app
           `exists_imp_exists
           [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
            (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])]))
         [])
        (group
         (tacticRwa__
          "rwa"
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff) "," (Tactic.rwRule [] `coe_pow)] "]")
          [(Tactic.location "at" (Tactic.locationHyp [`hk] ["⊢"]))])
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `exists_imp_exists
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
          (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])]))
       [])
      (group
       (tacticRwa__
        "rwa"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff) "," (Tactic.rwRule [] `coe_pow)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hk] ["⊢"]))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticRwa__
   "rwa"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.ext_iff) "," (Tactic.rwRule [] `coe_pow)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`hk] ["⊢"]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⊢»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `coe_pow
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subtype.ext_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `exists_imp_exists
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
     (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `exists_imp_exists
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
    (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.proj `S "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hc1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `hc1 [(Term.proj `S "." (fieldIdx "2")) (Term.anonymousCtor "⟨" [`g "," `hg] "⟩")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_"))) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exists_imp_exists
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
  (Term.anonymousCtor "⟨" [`g "," (Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hg] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `Carrier [])
      ":="
      (Set.Data.Set.Lattice.«term⋃_,_»
       "⋃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `R)] [":" `c]))
       ", "
       `R))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `one_mem' [])
      ":="
      (Term.anonymousCtor
       "⟨"
       [`Q "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩") "," `rfl] "⟩") "," `Q.one_mem]
       "⟩"))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `inv_mem' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`g] [])
         (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [`R
          ","
          (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
          ","
          (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])]
         "⟩"))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `mul_mem' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`g `h] [])
         (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
         (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hh] "⟩")]
        "=>"
        (Term.app
         (Term.proj
          (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
          "."
          `elim)
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`T] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [`S
              ","
              (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
              ","
              (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
             "⟩")))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`T] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [`R
              ","
              (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
              ","
              (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
             "⟩")))]))))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`g `h] [])
     (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
     (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hh] "⟩")]
    "=>"
    (Term.app
     (Term.proj
      (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
      "."
      `elim)
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`T] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [`S
          ","
          (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
          ","
          (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
         "⟩")))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`T] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [`R
          ","
          (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
          ","
          (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
         "⟩")))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
    "."
    `elim)
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`T] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [`S
        ","
        (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
        ","
        (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
       "⟩")))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`T] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [`R
        ","
        (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
        ","
        (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
       "⟩")))])
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
    [(Term.simpleBinder [`T] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [`R
      ","
      (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
      ","
      (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`R
    ","
    (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
    ","
    (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem) [`hg (Term.app `T [`hh])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `T [`hh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hh
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `T
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `T [`hh]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `mul_mem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `R "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
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
    [(Term.simpleBinder [`T] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [`S
      ","
      (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
      ","
      (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`S
    ","
    (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
    ","
    (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem) [(Term.app `T [`hg]) `hh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hh
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `T [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `T
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `T [`hg]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `S "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
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
    [(Term.simpleBinder [`T] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [`S
      ","
      (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
      ","
      (Term.app
       (Term.proj (Term.proj `S "." (fieldIdx "1")) "." `mul_mem)
       [(Term.paren "(" [(Term.app `T [`hg]) []] ")") `hh])]
     "⟩")))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
   "."
   `elim)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `S "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `R "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hc2.total_of_refl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `hc2.total_of_refl [(Term.proj `R "." (fieldIdx "2")) (Term.proj `S "." (fieldIdx "2"))]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩") "," `hh] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hh
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`S "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`g] [])
     (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [`R
      ","
      (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
      ","
      (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])]
     "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`R
    ","
    (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
    ","
    (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj `R "." (fieldIdx "1")) "." `inv_mem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `R "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
  (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩") "," `hg] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`R "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`Q "," (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩") "," `rfl] "⟩") "," `Q.one_mem]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Q.one_mem
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩") "," `rfl] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`Q "," `hQ] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hQ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Q
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Q
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `R)] [":" `c]))
   ", "
   `R)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/--
    A generalization of **Sylow's first theorem**.
      Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/
  theorem
    IsPGroup.exists_le_sylow
    { P : Subgroup G } ( hP : IsPGroup p P ) : ∃ Q : Sylow p G , P ≤ Q
    :=
      Exists.elim
        Zorn.zorn_nonempty_partial_order₀
            { Q : Subgroup G | IsPGroup p Q }
              fun
                c hc1 hc2 Q hQ
                  =>
                  ⟨
                    {
                        Carrier := ⋃ R : c , R ,
                          one_mem' := ⟨ Q , ⟨ ⟨ Q , hQ ⟩ , rfl ⟩ , Q.one_mem ⟩ ,
                          inv_mem' := fun g ⟨ _ , ⟨ R , rfl ⟩ , hg ⟩ => ⟨ R , ⟨ R , rfl ⟩ , R . 1 . inv_mem hg ⟩ ,
                          mul_mem'
                            :=
                            fun
                              g h ⟨ _ , ⟨ R , rfl ⟩ , hg ⟩ ⟨ _ , ⟨ S , rfl ⟩ , hh ⟩
                                =>
                                hc2.total_of_refl R . 2 S . 2 . elim
                                  fun T => ⟨ S , ⟨ S , rfl ⟩ , S . 1 . mul_mem T hg hh ⟩
                                    fun T => ⟨ R , ⟨ R , rfl ⟩ , R . 1 . mul_mem hg T hh ⟩
                        }
                      ,
                      fun
                        ⟨ g , _ , ⟨ S , rfl ⟩ , hg ⟩
                          =>
                          by
                            refine' exists_imp_exists fun k hk => _ hc1 S . 2 ⟨ g , hg ⟩
                              rwa [ Subtype.ext_iff , coe_pow ] at hk ⊢
                      ,
                      fun M hM g hg => ⟨ M , ⟨ ⟨ M , hM ⟩ , rfl ⟩ , hg ⟩
                    ⟩
              P
              hP
          fun Q ⟨ hQ1 , hQ2 , hQ3 ⟩ => ⟨ ⟨ Q , hQ1 , hQ3 ⟩ , hQ2 ⟩

instance Sylow.nonempty : Nonempty (Sylow p G) :=
  nonempty_of_exists IsPGroup.of_bot.exists_le_sylow

noncomputable instance Sylow.inhabited : Inhabited (Sylow p G) :=
  Classical.inhabitedOfNonempty Sylow.nonempty

open_locale Pointwise

-- failed to format: format: uncaught backtrack exception
/-- `subgroup.pointwise_mul_action` preserves Sylow subgroups. -/
  instance
    Sylow.pointwiseMulAction
    { α : Type _ } [ Groupₓ α ] [ MulDistribMulAction α G ] : MulAction α ( Sylow p G )
    where
      smul
          g P
          :=
          ⟨
            g • P
              ,
              P . 2 . map _
              ,
              fun
                Q hQ hS
                  =>
                  inv_smul_eq_iff . mp
                    (
                      P . 3
                        ( hQ.map _ )
                          fun
                            s hs
                              =>
                              ( congr_argₓ ( · ∈ g ⁻¹ • Q ) ( inv_smul_smul g s ) ) . mp
                                (
                                  smul_mem_pointwise_smul
                                    ( g • s ) ( g ⁻¹ ) Q ( hS ( smul_mem_pointwise_smul s g P hs ) )
                                  )
                      )
            ⟩
        one_smul P := Sylow.ext ( one_smul α P )
        mul_smul g h P := Sylow.ext ( mul_smul g h P )

theorem Sylow.pointwise_smul_def {α : Type _} [Groupₓ α] [MulDistribMulAction α G] {g : α} {P : Sylow p G} :
    ↑(g • P) = g • (P : Subgroup G) :=
  rfl

instance Sylow.mulAction : MulAction G (Sylow p G) :=
  comp_hom _ MulAut.conj

theorem Sylow.smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g • P :=
  rfl

theorem Sylow.coe_subgroup_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Subgroup G) :=
  rfl

theorem Sylow.coe_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Set G) :=
  rfl

theorem Sylow.smul_eq_iff_mem_normalizer {g : G} {P : Sylow p G} : g • P = P ↔ g ∈ P.1.normalizer := by
  rw [eq_comm, SetLike.ext_iff, ← inv_mem_iff, mem_normalizer_iff, inv_invₓ]
  exact
    forall_congrₓ fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ =>
          (congr_argₓ _ c).mp ((congr_argₓ (· ∈ P.1) (MulAut.inv_apply_self G (MulAut.conj g) a)).mpr b), fun hh =>
          ⟨(MulAut.conj g⁻¹) h, hh, MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩

theorem Subgroup.sylow_mem_fixed_points_iff (H : Subgroup G) {P : Sylow p G} :
    P ∈ fixed_points H (Sylow p G) ↔ H ≤ P.1.normalizer := by
  simp_rw [SetLike.le_def, ← Sylow.smul_eq_iff_mem_normalizer] <;> exact Subtype.forall

theorem IsPGroup.inf_normalizer_sylow {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G) : P⊓Q.1.normalizer = P⊓Q :=
  le_antisymmₓ
    (le_inf inf_le_left (sup_eq_right.mp (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)

theorem IsPGroup.sylow_mem_fixed_points_iff {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} :
    Q ∈ fixed_points P (Sylow p G) ↔ P ≤ Q := by
  rw [P.sylow_mem_fixed_points_iff, ← inf_eq_left, hP.inf_normalizer_sylow, inf_eq_left]

/--  A generalization of **Sylow's second theorem**.
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate. -/
instance [hp : Fact p.prime] [Fintype (Sylow p G)] : is_pretransitive G (Sylow p G) :=
  ⟨fun P Q => by
    classical
    have H := fun {R : Sylow p G} {S : orbit G P} =>
      calc S ∈ fixed_points R (orbit G P) ↔ S.1 ∈ fixed_points R (Sylow p G) := forall_congrₓ fun a => Subtype.ext_iff
        _ ↔ R.1 ≤ S := R.2.sylow_mem_fixed_points_iff
        _ ↔ S.1.1 = R := ⟨fun h => R.3 S.1.2 h, ge_of_eq⟩
        
    suffices Set.Nonempty (fixed_points Q (orbit G P))by
      exact Exists.elim this fun R hR => (congr_argₓ _ (Sylow.ext (H.mp hR))).mp R.2
    apply Q.2.nonempty_fixed_point_of_prime_not_dvd_card
    refine' fun h => hp.out.not_dvd_one (nat.modeq_zero_iff_dvd.mp _)
    calc 1 = card (fixed_points P (orbit G P)) := _ _ ≡ card (orbit G P) [MOD p] :=
      (P.2.card_modeq_card_fixed_points (orbit G P)).symm _ ≡ 0 [MOD p] := nat.modeq_zero_iff_dvd.mpr h
    convert (Set.card_singleton (⟨P, mem_orbit_self P⟩ : orbit G P)).symm
    exact set.eq_singleton_iff_unique_mem.mpr ⟨H.mpr rfl, fun R h => Subtype.ext (Sylow.ext (H.mp h))⟩⟩

variable (p) (G)

/--  A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`. -/
theorem card_sylow_modeq_one [Fact p.prime] [Fintype (Sylow p G)] : card (Sylow p G) ≡ 1 [MOD p] := by
  refine' sylow.nonempty.elim fun P : Sylow p G => _
  have :=
    Set.ext fun Q : Sylow p G =>
      calc Q ∈ fixed_points P (Sylow p G) ↔ P.1 ≤ Q := P.2.sylow_mem_fixed_points_iff
        _ ↔ Q.1 = P.1 := ⟨P.3 Q.2, ge_of_eq⟩
        _ ↔ Q ∈ {P} := sylow.ext_iff.symm.trans set.mem_singleton_iff.symm
        
  have : Fintype (fixed_points P.1 (Sylow p G)) := by
    convert Set.fintypeSingleton P
  have : card (fixed_points P.1 (Sylow p G)) = 1 := by
    convert Set.card_singleton P
  exact
    (P.2.card_modeq_card_fixed_points (Sylow p G)).trans
      (by
        rw [this])

variable {p} {G}

/--  Sylow subgroups are isomorphic -/
def Sylow.equivSmul (P : Sylow p G) (g : G) : P ≃* (g • P : Sylow p G) :=
  equiv_smul (MulAut.conj g) P.1

/--  Sylow subgroups are isomorphic -/
noncomputable def Sylow.equiv [Fact p.prime] [Fintype (Sylow p G)] (P Q : Sylow p G) : P ≃* Q := by
  rw [← Classical.some_spec (exists_smul_eq G P Q)]
  exact P.equiv_smul (Classical.some (exists_smul_eq G P Q))

@[simp]
theorem Sylow.orbit_eq_top [Fact p.prime] [Fintype (Sylow p G)] (P : Sylow p G) : orbit G P = ⊤ :=
  top_le_iff.mp fun Q hQ => exists_smul_eq G P Q

theorem Sylow.stabilizer_eq_normalizer (P : Sylow p G) : stabilizer G P = P.1.normalizer :=
  ext fun g => Sylow.smul_eq_iff_mem_normalizer

/--  Sylow `p`-subgroups are in bijection with cosets of the normalizer of a Sylow `p`-subgroup -/
noncomputable def Sylow.equivQuotientNormalizer [Fact p.prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    Sylow p G ≃ G ⧸ P.1.normalizer :=
  calc Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equivₓ.Set.univ (Sylow p G)).symm
    _ ≃ orbit G P := by
    rw [P.orbit_eq_top]
    _ ≃ G ⧸ stabilizer G P := orbit_equiv_quotient_stabilizer G P
    _ ≃ G ⧸ P.1.normalizer := by
    rw [P.stabilizer_eq_normalizer]
    

noncomputable instance [Fact p.prime] [Fintype (Sylow p G)] (P : Sylow p G) : Fintype (G ⧸ P.1.normalizer) :=
  of_equiv (Sylow p G) P.equiv_quotient_normalizer

theorem card_sylow_eq_card_quotient_normalizer [Fact p.prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    card (Sylow p G) = card (G ⧸ P.1.normalizer) :=
  card_congr P.equiv_quotient_normalizer

theorem card_sylow_eq_index_normalizer [Fact p.prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    card (Sylow p G) = P.1.normalizer.index :=
  (card_sylow_eq_card_quotient_normalizer P).trans P.1.normalizer.index_eq_card.symm

theorem card_sylow_dvd_index [Fact p.prime] [Fintype (Sylow p G)] (P : Sylow p G) : card (Sylow p G) ∣ P.1.index :=
  ((congr_argₓ _ (card_sylow_eq_index_normalizer P)).mp dvd_rfl).trans (index_dvd_of_le le_normalizer)

/--  Frattini's Argument: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
theorem Sylow.normalizer_sup_eq_top {p : ℕ} [Fact p.prime] {N : Subgroup G} [N.normal] [Fintype (Sylow p N)]
    (P : Sylow p N) : ((↑P : Subgroup N).map N.subtype).normalizer⊔N = ⊤ := by
  refine' top_le_iff.mp fun g hg => _
  obtain ⟨n, hn⟩ := exists_smul_eq N ((MulAut.conjNormal g : MulAut N) • P) P
  rw [← inv_mul_cancel_leftₓ (↑n) g, sup_comm]
  apply mul_mem_sup (N.inv_mem n.2)
  rw [Sylow.smul_def, ← mul_smul, ← MulAut.conj_normal_coe, ← mul_aut.conj_normal.map_mul, Sylow.ext_iff,
    Sylow.pointwise_smul_def, pointwise_smul_def] at hn
  refine' fun x =>
    (mem_map_iff_mem
            (show Function.Injective (MulAut.conj ((↑n)*g)).toMonoidHom from
              (MulAut.conj ((↑n)*g)).Injective)).symm.trans
      _
  rw [map_map, ← congr_argₓ (map N.subtype) hn, map_map]
  rfl

end InfiniteSylow

open Equivₓ Equivₓ.Perm Finset Function List QuotientGroup

open_locale BigOperators

universe u v w

variable {G : Type u} {α : Type v} {β : Type w} [Groupₓ G]

attribute [local instance] Subtype.fintype setFintype Classical.propDecidable

theorem QuotientGroup.card_preimage_mk [Fintype G] (s : Subgroup G) (t : Set (G ⧸ s)) :
    Fintype.card (QuotientGroup.mk ⁻¹' t) = Fintype.card s*Fintype.card t := by
  rw [← Fintype.card_prod, Fintype.card_congr (preimage_mk_equiv_subgroup_times_set _ _)]

namespace Sylow

open Subgroup Submonoid MulAction

theorem mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : Subgroup G} [Fintype ((H : Set G) : Type u)] {x : G} :
    (x : G ⧸ H) ∈ fixed_points H (G ⧸ H) ↔ x ∈ normalizer H :=
  ⟨fun hx =>
    have ha : ∀ {y : G ⧸ H}, y ∈ orbit H (x : G ⧸ H) → y = x := fun _ => (mem_fixed_points' _).1 hx _
    (inv_mem_iff _).1
      (@mem_normalizer_fintype _ _ _ _inst_2 _ fun n hn : n ∈ H =>
        have : ((n⁻¹*x)⁻¹*x) ∈ H := QuotientGroup.eq.1 (ha (mem_orbit _ ⟨n⁻¹, H.inv_mem hn⟩))
        show _ ∈ H by
          rw [mul_inv_rev, inv_invₓ] at this
          convert this
          rw [inv_invₓ]),
    fun hx : ∀ n : G, n ∈ H ↔ ((x*n)*x⁻¹) ∈ H =>
    (mem_fixed_points' _).2 $ fun y =>
      Quotientₓ.induction_on' y $ fun y hy =>
        QuotientGroup.eq.2
          (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy
          have hb₂ : ((b*x)⁻¹*y) ∈ H := QuotientGroup.eq.1 hb₂
          (inv_mem_iff H).1 $
            (hx _).2 $
              (mul_mem_cancel_left H (H.inv_mem hb₁)).1 $ by
                rw [hx] at hb₂ <;> simpa [mul_inv_rev, mul_assocₓ] using hb₂)⟩

def fixed_points_mul_left_cosets_equiv_quotient (H : Subgroup G) [Fintype (H : Set G)] :
    MulAction.FixedPoints H (G ⧸ H) ≃ normalizer H ⧸ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H :=
  @subtype_quotient_equiv_quotient_subtype G (normalizer H : Set G) (id _) (id _) (fixed_points _ _)
    (fun a => (@mem_fixed_points_mul_left_cosets_iff_mem_normalizer _ _ _ _inst_2 _).symm)
    (by
      intros <;> rfl)

/--  If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`.  -/
theorem card_quotient_normalizer_modeq_card_quotient [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.prime] {H : Subgroup G}
    (hH : Fintype.card H = (p^n)) :
    card (normalizer H ⧸ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H) ≡ card (G ⧸ H) [MOD p] := by
  rw [← Fintype.card_congr (fixed_points_mul_left_cosets_equiv_quotient H)]
  exact ((IsPGroup.of_card hH).card_modeq_card_fixed_points _).symm

/--  If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`.  -/
theorem card_normalizer_modeq_card [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.prime] {H : Subgroup G}
    (hH : Fintype.card H = (p^n)) : card (normalizer H) ≡ card G [MOD p^n+1] :=
  have : Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H ≃ H :=
    Set.BijOn.equiv (normalizer H).Subtype
      ⟨fun _ => id, fun _ _ _ _ h => Subtype.val_injective h, fun x hx => ⟨⟨x, le_normalizer hx⟩, hx, rfl⟩⟩
  by
  rw [card_eq_card_quotient_mul_card_subgroup H,
    card_eq_card_quotient_mul_card_subgroup (Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H),
    Fintype.card_congr this, hH, pow_succₓ]
  exact (card_quotient_normalizer_modeq_card_quotient hH).mul_right' _

/--  If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
theorem prime_dvd_card_quotient_normalizer [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.prime] (hdvd : (p^n+1) ∣ card G)
    {H : Subgroup G} (hH : Fintype.card H = (p^n)) :
    p ∣ card (normalizer H ⧸ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H) :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : card (G ⧸ H) = s*p :=
    (Nat.mul_left_inj (show card H > 0 from Fintype.card_pos_iff.2 ⟨⟨1, H.one_mem⟩⟩)).1
      (by
        rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ'ₓ, mul_assocₓ, mul_commₓ p])
  have hm : (s*p) % p = card (normalizer H ⧸ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H) % p :=
    hcard ▸ (card_quotient_normalizer_modeq_card_quotient hH).symm
  Nat.dvd_of_mod_eq_zeroₓ
    (by
      rwa [Nat.mod_eq_zero_of_dvdₓ (dvd_mul_left _ _), eq_comm] at hm)

/--  If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
theorem prime_pow_dvd_card_normalizer [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.prime] (hdvd : (p^n+1) ∣ card G)
    {H : Subgroup G} (hH : Fintype.card H = (p^n)) : (p^n+1) ∣ card (normalizer H) :=
  Nat.modeq_zero_iff_dvd.1 ((card_normalizer_modeq_card hH).trans hdvd.modeq_zero_nat)

/--  If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.prime] (hdvd : (p^n+1) ∣ card G)
    {H : Subgroup G} (hH : Fintype.card H = (p^n)) : ∃ K : Subgroup G, Fintype.card K = (p^n+1) ∧ H ≤ K :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : card (G ⧸ H) = s*p :=
    (Nat.mul_left_inj (show card H > 0 from Fintype.card_pos_iff.2 ⟨⟨1, H.one_mem⟩⟩)).1
      (by
        rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ'ₓ, mul_assocₓ, mul_commₓ p])
  have hm : (s*p) % p = card (normalizer H ⧸ Subgroup.comap (normalizer H).Subtype H) % p :=
    card_congr (fixed_points_mul_left_cosets_equiv_quotient H) ▸
      hcard ▸ (IsPGroup.of_card hH).card_modeq_card_fixed_points _
  have hm' : p ∣ card (normalizer H ⧸ Subgroup.comap (normalizer H).Subtype H) :=
    Nat.dvd_of_mod_eq_zeroₓ
      (by
        rwa [Nat.mod_eq_zero_of_dvdₓ (dvd_mul_left _ _), eq_comm] at hm)
  let ⟨x, hx⟩ := @exists_prime_order_of_dvd_card _ (QuotientGroup.Quotient.group _) _ _ hp hm'
  have hequiv : H ≃ Subgroup.comap ((normalizer H).Subtype : normalizer H →* G) H :=
    ⟨fun a => ⟨⟨a.1, le_normalizer a.2⟩, a.2⟩, fun a => ⟨a.1.1, a.2⟩, fun ⟨_, _⟩ => rfl, fun ⟨⟨_, _⟩, _⟩ => rfl⟩
  ⟨Subgroup.map (normalizer H).Subtype (Subgroup.comap (QuotientGroup.mk' (comap H.normalizer.subtype H)) (zpowers x)),
    by
    show card (↥map H.normalizer.subtype (comap (mk' (comap H.normalizer.subtype H)) (Subgroup.zpowers x))) = (p^n+1)
    suffices
      card (↥(Subtype.val '' (Subgroup.comap (mk' (comap H.normalizer.subtype H)) (zpowers x) : Set (↥H.normalizer)))) =
        (p^n+1)by
      convert this using 2
    rw
      [Set.card_image_of_injective (Subgroup.comap (mk' (comap H.normalizer.subtype H)) (zpowers x) : Set H.normalizer)
        Subtype.val_injective,
      pow_succ'ₓ, ← hH, Fintype.card_congr hequiv, ← hx, order_eq_card_zpowers, ← Fintype.card_prod]
    exact @Fintype.card_congr _ _ (id _) (id _) (preimage_mk_equiv_subgroup_times_set _ _), by
    intro y hy
    simp only [exists_prop, Subgroup.coe_subtype, mk'_apply, Subgroup.mem_map, Subgroup.mem_comap]
    refine' ⟨⟨y, le_normalizer hy⟩, ⟨0, _⟩, rfl⟩
    rw [zpow_zero, eq_comm, QuotientGroup.eq_one_iff]
    simpa using hy⟩

/--  If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [Fintype G] (p : ℕ) :
    ∀ {n m : ℕ} [hp : Fact p.prime] hdvd : (p^m) ∣ card G H : Subgroup G hH : card H = (p^n) hnm : n ≤ m,
      ∃ K : Subgroup G, card K = (p^m) ∧ H ≤ K
  | n, m => fun hp hdvd H hH hnm =>
    (lt_or_eq_of_leₓ hnm).elim
      (fun hnm : n < m =>
        have h0m : 0 < m := lt_of_le_of_ltₓ n.zero_le hnm
        have wf : m - 1 < m := Nat.sub_ltₓ h0m zero_lt_one
        have hnm1 : n ≤ m - 1 := le_tsub_of_add_le_right hnm
        let ⟨K, hK⟩ :=
          @exists_subgroup_card_pow_prime_le n (m - 1) hp (Nat.pow_dvd_of_le_of_pow_dvd tsub_le_self hdvd) H hH hnm1
        have hdvd' : (p^(m - 1)+1) ∣ card G := by
          rwa [tsub_add_cancel_of_le h0m.nat_succ_le]
        let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ hp hdvd' K hK.1
        ⟨K', by
          rw [hK'.1, tsub_add_cancel_of_le h0m.nat_succ_le], le_transₓ hK.2 hK'.2⟩)
      fun hnm : n = m =>
      ⟨H, by
        simp [hH, hnm]⟩

/--  A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
theorem exists_subgroup_card_pow_prime [Fintype G] (p : ℕ) {n : ℕ} [Fact p.prime] (hdvd : (p^n) ∣ card G) :
    ∃ K : Subgroup G, Fintype.card K = (p^n) :=
  let ⟨K, hK⟩ :=
    exists_subgroup_card_pow_prime_le p hdvd ⊥
      (by
        simp )
      n.zero_le
  ⟨K, hK.1⟩

theorem pow_dvd_card_of_pow_dvd_card [Fintype G] {p n : ℕ} [Fact p.prime] (P : Sylow p G) (hdvd : (p^n) ∣ card G) :
    (p^n) ∣ card P := by
  obtain ⟨Q, hQ⟩ := exists_subgroup_card_pow_prime p hdvd
  obtain ⟨R, hR⟩ := (IsPGroup.of_card hQ).exists_le_sylow
  obtain ⟨g, rfl⟩ := exists_smul_eq G R P
  calc (p^n) = card Q := hQ.symm _ ∣ card R := card_dvd_of_le hR _ = card (g • R) := card_congr (R.equiv_smul g).toEquiv

theorem dvd_card_of_dvd_card [Fintype G] {p : ℕ} [Fact p.prime] (P : Sylow p G) (hdvd : p ∣ card G) : p ∣ card P := by
  rw [← pow_oneₓ p] at hdvd
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd
  rwa [pow_oneₓ] at key

theorem ne_bot_of_dvd_card [Fintype G] {p : ℕ} [hp : Fact p.prime] (P : Sylow p G) (hdvd : p ∣ card G) :
    (P : Subgroup G) ≠ ⊥ := by
  refine' fun h => hp.out.not_dvd_one _
  have key : p ∣ card (P : Subgroup G) := P.dvd_card_of_dvd_card hdvd
  rwa [h, card_bot] at key

end Sylow

