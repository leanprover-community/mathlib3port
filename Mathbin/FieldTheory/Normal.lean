import Mathbin.FieldTheory.Adjoin
import Mathbin.FieldTheory.Tower
import Mathbin.GroupTheory.Solvable
import Mathbin.RingTheory.PowerBasis

/-!
# Normal field extensions

In this file we define normal field extensions and prove that for a finite extension, being normal
is the same as being a splitting field (`normal.of_is_splitting_field` and
`normal.exists_is_splitting_field`).

## Main Definitions

- `normal F K` where `K` is a field extension of `F`.
-/


noncomputable section

open_locale BigOperators

open_locale Classical

open Polynomial IsScalarTower

variable (F K : Type _) [Field F] [Field K] [Algebra F K]

/--  Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
class Normal : Prop where
  is_integral' (x : K) : IsIntegral F x
  splits' (x : K) : splits (algebraMap F K) (minpoly F x)

variable {F K}

theorem Normal.is_integral (h : Normal F K) (x : K) : IsIntegral F x :=
  Normal.is_integral' x

theorem Normal.splits (h : Normal F K) (x : K) : splits (algebraMap F K) (minpoly F x) :=
  Normal.splits' x

theorem normal_iff : Normal F K ↔ ∀ x : K, IsIntegral F x ∧ splits (algebraMap F K) (minpoly F x) :=
  ⟨fun h x => ⟨h.is_integral x, h.splits x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩

theorem Normal.out : Normal F K → ∀ x : K, IsIntegral F x ∧ splits (algebraMap F K) (minpoly F x) :=
  normal_iff.1

variable (F K)

instance normal_self : Normal F F :=
  ⟨fun x => is_integral_algebra_map, fun x => by
    rw [minpoly.eq_X_sub_C']
    exact splits_X_sub_C _⟩

variable {K}

variable (K)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Normal.exists_is_splitting_field [])
  (Command.declSig
   [(Term.instBinder "[" [`h ":"] (Term.app `Normal [`F `K]) "]")
    (Term.instBinder "[" [] (Term.app `FiniteDimensional [`F `K]) "]")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `p)] [":" (Term.app `Polynomial [`F])]))
     ","
     (Term.app `is_splitting_field [`F `K `p]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `s [] ":=" (Term.app `Basis.ofVectorSpace [`F `K]))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Algebra.BigOperators.Basic.«term∏_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            ", "
            (Term.app `minpoly [`F (Term.app `s [`x])]))
           ","
           («term_$__»
            (Term.app `splits_prod [(Term.hole "_")])
            "$"
            (Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `h.splits [(Term.app `s [`x])]))))
           ","
           (Term.app `Subalgebra.to_submodule_injective [(Term.hole "_")])]
          "⟩"))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Algebra.top_to_submodule)
           ","
           (Tactic.rwRule [] `eq_top_iff)
           ","
           (Tactic.rwRule ["←"] `s.span_eq)
           ","
           (Tactic.rwRule [] `Submodule.span_le)
           ","
           (Tactic.rwRule [] `Set.range_subset_iff)]
          "]")
         [])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.app
            `Algebra.subset_adjoin
            [(«term_$__»
              `multiset.mem_to_finset.mpr
              "$"
              (Term.app
               (Term.proj
                («term_$__»
                 `mem_roots
                 "$"
                 («term_$__»
                  (Term.app
                   `mt
                   [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
                  "$"
                  («term_$__»
                   (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
                   "$"
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
                "."
                (fieldIdx "2"))
               [(Term.hole "_")]))]))))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.exact "exact" (Term.app `minpoly.ne_zero [(Term.app `h.is_integral [(Term.app `s [`x])])]))
             [])])))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `is_root.def)
           ","
           (Tactic.rwRule [] `eval_map)
           ","
           (Tactic.rwRule ["←"] `aeval_def)
           ","
           (Tactic.rwRule [] `AlgHom.map_prod)]
          "]")
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `Finset.prod_eq_zero
          [(Term.app `Finset.mem_univ [(Term.hole "_")]) (Term.app `minpoly.aeval [(Term.hole "_") (Term.hole "_")])]))
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
       (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `s [] ":=" (Term.app `Basis.ofVectorSpace [`F `K]))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Algebra.BigOperators.Basic.«term∏_,_»
           "∏"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           ", "
           (Term.app `minpoly [`F (Term.app `s [`x])]))
          ","
          («term_$__»
           (Term.app `splits_prod [(Term.hole "_")])
           "$"
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `h.splits [(Term.app `s [`x])]))))
          ","
          (Term.app `Subalgebra.to_submodule_injective [(Term.hole "_")])]
         "⟩"))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Algebra.top_to_submodule)
          ","
          (Tactic.rwRule [] `eq_top_iff)
          ","
          (Tactic.rwRule ["←"] `s.span_eq)
          ","
          (Tactic.rwRule [] `Submodule.span_le)
          ","
          (Tactic.rwRule [] `Set.range_subset_iff)]
         "]")
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.app
           `Algebra.subset_adjoin
           [(«term_$__»
             `multiset.mem_to_finset.mpr
             "$"
             (Term.app
              (Term.proj
               («term_$__»
                `mem_roots
                "$"
                («term_$__»
                 (Term.app
                  `mt
                  [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
                 "$"
                 («term_$__»
                  (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
                  "$"
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
               "."
               (fieldIdx "2"))
              [(Term.hole "_")]))]))))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact "exact" (Term.app `minpoly.ne_zero [(Term.app `h.is_integral [(Term.app `s [`x])])]))
            [])])))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `is_root.def)
          ","
          (Tactic.rwRule [] `eval_map)
          ","
          (Tactic.rwRule ["←"] `aeval_def)
          ","
          (Tactic.rwRule [] `AlgHom.map_prod)]
         "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `Finset.prod_eq_zero
         [(Term.app `Finset.mem_univ [(Term.hole "_")]) (Term.app `minpoly.aeval [(Term.hole "_") (Term.hole "_")])]))
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
    `Finset.prod_eq_zero
    [(Term.app `Finset.mem_univ [(Term.hole "_")]) (Term.app `minpoly.aeval [(Term.hole "_") (Term.hole "_")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.prod_eq_zero
   [(Term.app `Finset.mem_univ [(Term.hole "_")]) (Term.app `minpoly.aeval [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.aeval [(Term.hole "_") (Term.hole "_")])
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
  `minpoly.aeval
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `minpoly.aeval [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Finset.mem_univ [(Term.hole "_")])
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
  `Finset.mem_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finset.mem_univ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.prod_eq_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
    [(Tactic.rwRule [] `is_root.def)
     ","
     (Tactic.rwRule [] `eval_map)
     ","
     (Tactic.rwRule ["←"] `aeval_def)
     ","
     (Tactic.rwRule [] `AlgHom.map_prod)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgHom.map_prod
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `aeval_def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_root.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.exact "exact" (Term.app `minpoly.ne_zero [(Term.app `h.is_integral [(Term.app `s [`x])])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `minpoly.ne_zero [(Term.app `h.is_integral [(Term.app `s [`x])])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.ne_zero [(Term.app `h.is_integral [(Term.app `s [`x])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h.is_integral [(Term.app `s [`x])])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h.is_integral
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `h.is_integral [(Term.paren "(" [(Term.app `s [`x]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.ne_zero
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
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x] [])]
     "=>"
     (Term.app
      `Algebra.subset_adjoin
      [(«term_$__»
        `multiset.mem_to_finset.mpr
        "$"
        (Term.app
         (Term.proj
          («term_$__»
           `mem_roots
           "$"
           («term_$__»
            (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
            "$"
            («term_$__»
             (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
             "$"
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
          "."
          (fieldIdx "2"))
         [(Term.hole "_")]))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.app
     `Algebra.subset_adjoin
     [(«term_$__»
       `multiset.mem_to_finset.mpr
       "$"
       (Term.app
        (Term.proj
         («term_$__»
          `mem_roots
          "$"
          («term_$__»
           (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
           "$"
           («term_$__»
            (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
            "$"
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
         "."
         (fieldIdx "2"))
        [(Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Algebra.subset_adjoin
   [(«term_$__»
     `multiset.mem_to_finset.mpr
     "$"
     (Term.app
      (Term.proj
       («term_$__»
        `mem_roots
        "$"
        («term_$__»
         (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
         "$"
         («term_$__»
          (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
          "$"
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
       "."
       (fieldIdx "2"))
      [(Term.hole "_")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `multiset.mem_to_finset.mpr
   "$"
   (Term.app
    (Term.proj
     («term_$__»
      `mem_roots
      "$"
      («term_$__»
       (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
       "$"
       («term_$__»
        (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
        "$"
        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
     "."
     (fieldIdx "2"))
    [(Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    («term_$__»
     `mem_roots
     "$"
     («term_$__»
      (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
      "$"
      («term_$__»
       (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
       "$"
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
    "."
    (fieldIdx "2"))
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
   («term_$__»
    `mem_roots
    "$"
    («term_$__»
     (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
     "$"
     («term_$__»
      (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
      "$"
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
   "."
   (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_$__»
   `mem_roots
   "$"
   («term_$__»
    (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
    "$"
    («term_$__»
     (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
     "$"
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
   "$"
   («term_$__»
    (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
    "$"
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Finset.prod_ne_zero_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app `mt [(Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `algebraMap [`F `K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `algebraMap
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `map_eq_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `mem_roots
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__»
   `mem_roots
   "$"
   («term_$__»
    (Term.app
     `mt
     [(Term.proj
       (Term.paren "(" [(«term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) []] ")")
       "."
       (fieldIdx "1"))])
    "$"
    («term_$__»
     (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
     "$"
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `multiset.mem_to_finset.mpr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__»
   `multiset.mem_to_finset.mpr
   "$"
   (Term.app
    (Term.proj
     (Term.paren
      "("
      [(«term_$__»
        `mem_roots
        "$"
        («term_$__»
         (Term.app
          `mt
          [(Term.proj
            (Term.paren "(" [(«term_$__» `map_eq_zero "$" (Term.app `algebraMap [`F `K])) []] ")")
            "."
            (fieldIdx "1"))])
         "$"
         («term_$__»
          (Term.proj `Finset.prod_ne_zero_iff "." (fieldIdx "2"))
          "$"
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.hole "_"))))))
       []]
      ")")
     "."
     (fieldIdx "2"))
    [(Term.hole "_")]))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Algebra.subset_adjoin
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `Algebra.top_to_submodule)
     ","
     (Tactic.rwRule [] `eq_top_iff)
     ","
     (Tactic.rwRule ["←"] `s.span_eq)
     ","
     (Tactic.rwRule [] `Submodule.span_le)
     ","
     (Tactic.rwRule [] `Set.range_subset_iff)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.range_subset_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Submodule.span_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s.span_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_top_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Algebra.top_to_submodule
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Algebra.BigOperators.Basic.«term∏_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
      ", "
      (Term.app `minpoly [`F (Term.app `s [`x])]))
     ","
     («term_$__»
      (Term.app `splits_prod [(Term.hole "_")])
      "$"
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `h.splits [(Term.app `s [`x])]))))
     ","
     (Term.app `Subalgebra.to_submodule_injective [(Term.hole "_")])]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Algebra.BigOperators.Basic.«term∏_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     ", "
     (Term.app `minpoly [`F (Term.app `s [`x])]))
    ","
    («term_$__»
     (Term.app `splits_prod [(Term.hole "_")])
     "$"
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `h.splits [(Term.app `s [`x])]))))
    ","
    (Term.app `Subalgebra.to_submodule_injective [(Term.hole "_")])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Subalgebra.to_submodule_injective [(Term.hole "_")])
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
  `Subalgebra.to_submodule_injective
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `splits_prod [(Term.hole "_")])
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `h.splits [(Term.app `s [`x])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `hx] [])] "=>" (Term.app `h.splits [(Term.app `s [`x])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h.splits [(Term.app `s [`x])])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h.splits
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app `splits_prod [(Term.hole "_")])
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
  `splits_prod
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_,_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   ", "
   (Term.app `minpoly [`F (Term.app `s [`x])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly [`F (Term.app `s [`x])])
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
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  Normal.exists_is_splitting_field
  [ h : Normal F K ] [ FiniteDimensional F K ] : ∃ p : Polynomial F , is_splitting_field F K p
  :=
    by
      let s := Basis.ofVectorSpace F K
        refine' ⟨ ∏ x , minpoly F s x , splits_prod _ $ fun x hx => h.splits s x , Subalgebra.to_submodule_injective _ ⟩
        rw [ Algebra.top_to_submodule , eq_top_iff , ← s.span_eq , Submodule.span_le , Set.range_subset_iff ]
        refine'
          fun
            x
              =>
              Algebra.subset_adjoin
                multiset.mem_to_finset.mpr
                  $
                  mem_roots $ mt map_eq_zero $ algebraMap F K . 1 $ Finset.prod_ne_zero_iff . 2 $ fun x hx => _ . 2 _
        · exact minpoly.ne_zero h.is_integral s x
        rw [ is_root.def , eval_map , ← aeval_def , AlgHom.map_prod ]
        exact Finset.prod_eq_zero Finset.mem_univ _ minpoly.aeval _ _

section NormalTower

variable (E : Type _) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

theorem Normal.tower_top_of_normal [h : Normal F E] : Normal K E :=
  normal_iff.2 $ fun x => by
    cases' h.out x with hx hhx
    rw [algebra_map_eq F K E] at hhx
    exact
      ⟨is_integral_of_is_scalar_tower x hx,
        Polynomial.splits_of_splits_of_dvd (algebraMap K E) (Polynomial.map_ne_zero (minpoly.ne_zero hx))
          ((Polynomial.splits_map_iff (algebraMap F K) (algebraMap K E)).mpr hhx)
          (minpoly.dvd_map_of_is_scalar_tower F K x)⟩

theorem AlgHom.normal_bijective [h : Normal F E] (ϕ : E →ₐ[F] K) : Function.Bijective ϕ :=
  ⟨ϕ.to_ring_hom.injective, fun x => by
    let this' : Algebra E K := ϕ.to_ring_hom.to_algebra
    obtain ⟨h1, h2⟩ := h.out (algebraMap K E x)
    cases'
      minpoly.mem_range_of_degree_eq_one E x
        (Or.resolve_left h2 (minpoly.ne_zero h1)
          (minpoly.irreducible
            (is_integral_of_is_scalar_tower x ((is_integral_algebra_map_iff (algebraMap K E).Injective).mp h1)))
          (minpoly.dvd E x
            ((algebraMap K E).Injective
              (by
                rw [RingHom.map_zero, aeval_map, ← IsScalarTower.to_alg_hom_apply F K E, ← AlgHom.comp_apply, ←
                  aeval_alg_hom]
                exact minpoly.aeval F (algebraMap K E x))))) with
      y hy
    exact ⟨y, hy⟩⟩

variable {F} {E} {E' : Type _} [Field E'] [Algebra F E']

theorem Normal.of_alg_equiv [h : Normal F E] (f : E ≃ₐ[F] E') : Normal F E' :=
  normal_iff.2 $ fun x => by
    cases' h.out (f.symm x) with hx hhx
    have H := is_integral_alg_hom f.to_alg_hom hx
    rw [AlgEquiv.to_alg_hom_eq_coe, AlgEquiv.coe_alg_hom, AlgEquiv.apply_symm_apply] at H
    use H
    apply Polynomial.splits_of_splits_of_dvd (algebraMap F E') (minpoly.ne_zero hx)
    ·
      rw [← AlgHom.comp_algebra_map f.to_alg_hom]
      exact Polynomial.splits_comp_of_splits (algebraMap F E) f.to_alg_hom.to_ring_hom hhx
    ·
      apply minpoly.dvd _ _
      rw [← AddEquiv.map_eq_zero_iff f.symm.to_add_equiv]
      exact
        Eq.trans (Polynomial.aeval_alg_hom_apply f.symm.to_alg_hom x (minpoly F (f.symm x))).symm (minpoly.aeval _ _)

theorem AlgEquiv.transfer_normal (f : E ≃ₐ[F] E') : Normal F E ↔ Normal F E' :=
  ⟨fun h => by
    exact Normal.of_alg_equiv f, fun h => by
    exact Normal.of_alg_equiv f.symm⟩

theorem Normal.of_is_splitting_field (p : Polynomial F) [hFEp : is_splitting_field F E p] : Normal F E := by
  by_cases' hp : p = 0
  ·
    have : is_splitting_field F F p := by
      rw [hp]
      exact ⟨splits_zero _, Subsingleton.elimₓ _ _⟩
    exact
      (AlgEquiv.transfer_normal ((is_splitting_field.alg_equiv F p).trans (is_splitting_field.alg_equiv E p).symm)).mp
        (normal_self F)
  refine' normal_iff.2 fun x => _
  have hFE : FiniteDimensional F E := is_splitting_field.finite_dimensional E p
  have Hx : IsIntegral F x := is_integral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x
  refine' ⟨Hx, Or.inr _⟩
  rintro q q_irred ⟨r, hr⟩
  let D := AdjoinRoot q
  let pbED := AdjoinRoot.powerBasis q_irred.ne_zero
  have : FiniteDimensional E D := PowerBasis.finite_dimensional pbED
  have finrankED : FiniteDimensional.finrank E D = q.nat_degree := PowerBasis.finrank pbED
  let this' : Algebra F D := RingHom.toAlgebra ((algebraMap E D).comp (algebraMap F E))
  have : IsScalarTower F E D := of_algebra_map_eq fun _ => rfl
  have : FiniteDimensional F D := FiniteDimensional.trans F E D
  suffices Nonempty (D →ₐ[F] E)by
    cases' this with ϕ
    rw [← WithBot.coe_one, degree_eq_iff_nat_degree_eq q_irred.ne_zero, ← finrankED]
    have nat_lemma : ∀ a b c : ℕ, (a*b) = c → c ≤ a → 0 < c → b = 1 := by
      intro a b c h1 h2 h3
      nlinarith
    exact
      nat_lemma _ _ _ (FiniteDimensional.finrank_mul_finrank F E D)
        (LinearMap.finrank_le_finrank_of_injective
          (show Function.Injective ϕ.to_linear_map from ϕ.to_ring_hom.injective))
        FiniteDimensional.finrank_pos
  let C := AdjoinRoot (minpoly F x)
  have Hx_irred := minpoly.irreducible Hx
  let this' : Algebra C D :=
    RingHom.toAlgebra
      (AdjoinRoot.lift (algebraMap F D) (AdjoinRoot.root q)
        (by
          rw [algebra_map_eq F E D, ← eval₂_map, hr, AdjoinRoot.algebra_map_eq, eval₂_mul, AdjoinRoot.eval₂_root,
            zero_mul]))
  let this' : Algebra C E := RingHom.toAlgebra (AdjoinRoot.lift (algebraMap F E) x (minpoly.aeval F x))
  have : IsScalarTower F C D := of_algebra_map_eq fun x => (AdjoinRoot.lift_of _).symm
  have : IsScalarTower F C E := of_algebra_map_eq fun x => (AdjoinRoot.lift_of _).symm
  suffices Nonempty (D →ₐ[C] E)by
    exact Nonempty.map (AlgHom.restrictScalars F) this
  let S : Set D := ((p.map (algebraMap F E)).roots.map (algebraMap E D)).toFinset
  suffices ⊤ ≤ IntermediateField.adjoin C S by
    refine' IntermediateField.alg_hom_mk_adjoin_splits' (top_le_iff.mp this) fun y hy => _
    rcases multiset.mem_map.mp (multiset.mem_to_finset.mp hy) with ⟨z, hz1, hz2⟩
    have Hz : IsIntegral F z := is_integral_of_noetherian (IsNoetherian.iff_fg.2 hFE) z
    use show IsIntegral C y from is_integral_of_noetherian (IsNoetherian.iff_fg.2 (FiniteDimensional.right F C D)) y
    apply splits_of_splits_of_dvd (algebraMap C E) (map_ne_zero (minpoly.ne_zero Hz))
    ·
      rw [splits_map_iff, ← algebra_map_eq F C E]
      exact
        splits_of_splits_of_dvd _ hp hFEp.splits
          (minpoly.dvd F z (Eq.trans (eval₂_eq_eval_map _) ((mem_roots (map_ne_zero hp)).mp hz1)))
    ·
      apply minpoly.dvd
      rw [← hz2, aeval_def, eval₂_map, ← algebra_map_eq F C D, algebra_map_eq F E D, ← hom_eval₂, ← aeval_def,
        minpoly.aeval F z, RingHom.map_zero]
  rw [← IntermediateField.to_subalgebra_le_to_subalgebra, IntermediateField.top_to_subalgebra]
  apply ge_transₓ (IntermediateField.algebra_adjoin_le_adjoin C S)
  suffices (Algebra.adjoin C S).restrictScalars F = (Algebra.adjoin E {AdjoinRoot.root q}).restrictScalars F by
    rw [AdjoinRoot.adjoin_root_eq_top, Subalgebra.restrict_scalars_top, ← @Subalgebra.restrict_scalars_top F C] at this
    exact top_le_iff.mpr (Subalgebra.restrict_scalars_injective F this)
  dsimp only [S]
  rw [← Finset.image_to_finset, Finset.coe_image]
  apply Eq.trans (Algebra.adjoin_res_eq_adjoin_res F E C D hFEp.adjoin_roots AdjoinRoot.adjoin_root_eq_top)
  rw [Set.image_singleton, RingHom.algebra_map_to_algebra, AdjoinRoot.lift_root]

instance (p : Polynomial F) : Normal F p.splitting_field :=
  Normal.of_is_splitting_field p

end NormalTower

variable {F} {K} (ϕ ψ : K →ₐ[F] K) (χ ω : K ≃ₐ[F] K)

section Restrict

variable (E : Type _) [Field E] [Algebra F E] [Algebra E K] [IsScalarTower F E K]

/--  Restrict algebra homomorphism to image of normal subfield -/
def AlgHom.restrictNormalAux [h : Normal F E] : (to_alg_hom F E K).range →ₐ[F] (to_alg_hom F E K).range :=
  { toFun := fun x =>
      ⟨ϕ x, by
        suffices (to_alg_hom F E K).range.map ϕ ≤ _ by
          exact this ⟨x, Subtype.mem x, rfl⟩
        rintro x ⟨y, ⟨z, hy⟩, hx⟩
        rw [← hx, ← hy]
        apply minpoly.mem_range_of_degree_eq_one E
        exact
          Or.resolve_left (h.splits z) (minpoly.ne_zero (h.is_integral z))
            (minpoly.irreducible $
              is_integral_of_is_scalar_tower _ $ is_integral_alg_hom ϕ $ is_integral_alg_hom _ $ h.is_integral z)
            (minpoly.dvd E _ $ by
              rw [aeval_map, aeval_alg_hom, aeval_alg_hom, AlgHom.comp_apply, AlgHom.comp_apply, minpoly.aeval,
                AlgHom.map_zero, AlgHom.map_zero])⟩,
    map_zero' := Subtype.ext ϕ.map_zero, map_one' := Subtype.ext ϕ.map_one,
    map_add' := fun x y => Subtype.ext (ϕ.map_add x y), map_mul' := fun x y => Subtype.ext (ϕ.map_mul x y),
    commutes' := fun x => Subtype.ext (ϕ.commutes x) }

/--  Restrict algebra homomorphism to normal subfield -/
def AlgHom.restrictNormal [Normal F E] : E →ₐ[F] E :=
  ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)).symm.toAlgHom.comp (ϕ.restrict_normal_aux E)).comp
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)).toAlgHom

@[simp]
theorem AlgHom.restrict_normal_commutes [Normal F E] (x : E) :
    algebraMap E K (ϕ.restrict_normal E x) = ϕ (algebraMap E K x) :=
  Subtype.ext_iff.mp
    (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K))
      (ϕ.restrict_normal_aux E ⟨IsScalarTower.toAlgHom F E K x, x, rfl⟩))

theorem AlgHom.restrict_normal_comp [Normal F E] :
    (ϕ.restrict_normal E).comp (ψ.restrict_normal E) = (ϕ.comp ψ).restrictNormal E :=
  AlgHom.ext fun _ =>
    (algebraMap E K).Injective
      (by
        simp only [AlgHom.comp_apply, AlgHom.restrict_normal_commutes])

/--  Restrict algebra isomorphism to a normal subfield -/
def AlgEquiv.restrictNormal [h : Normal F E] : E ≃ₐ[F] E :=
  AlgEquiv.ofBijective (χ.to_alg_hom.restrict_normal E) (AlgHom.normal_bijective F E E _)

@[simp]
theorem AlgEquiv.restrict_normal_commutes [Normal F E] (x : E) :
    algebraMap E K (χ.restrict_normal E x) = χ (algebraMap E K x) :=
  χ.to_alg_hom.restrict_normal_commutes E x

theorem AlgEquiv.restrict_normal_trans [Normal F E] :
    (χ.trans ω).restrictNormal E = (χ.restrict_normal E).trans (ω.restrict_normal E) :=
  AlgEquiv.ext fun _ =>
    (algebraMap E K).Injective
      (by
        simp only [AlgEquiv.trans_apply, AlgEquiv.restrict_normal_commutes])

/--  Restriction to an normal subfield as a group homomorphism -/
def AlgEquiv.restrictNormalHom [Normal F E] : (K ≃ₐ[F] K) →* E ≃ₐ[F] E :=
  MonoidHom.mk' (fun χ => χ.restrict_normal E) fun ω χ => χ.restrict_normal_trans ω E

end Restrict

section lift

variable {F} {K} (E : Type _) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

/--  If `E/K/F` is a tower of fields with `E/F` normal then we can lift
  an algebra homomorphism `ϕ : K →ₐ[F] K` to `ϕ.lift_normal E : E →ₐ[F] E`. -/
noncomputable def AlgHom.liftNormal [h : Normal F E] : E →ₐ[F] E :=
  @AlgHom.restrictScalars F K E E _ _ _ _ _ _ ((IsScalarTower.toAlgHom F K E).comp ϕ).toRingHom.toAlgebra _ _ _ _
    (Nonempty.some
      (@IntermediateField.alg_hom_mk_adjoin_splits' K E E _ _ _ _
        ((IsScalarTower.toAlgHom F K E).comp ϕ).toRingHom.toAlgebra ⊤ rfl fun x hx =>
        ⟨is_integral_of_is_scalar_tower x (h.out x).1,
          splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero (h.out x).1))
            (by
              rw [splits_map_iff, ← IsScalarTower.algebra_map_eq]
              exact (h.out x).2)
            (minpoly.dvd_map_of_is_scalar_tower F K x)⟩))

@[simp]
theorem AlgHom.lift_normal_commutes [Normal F E] (x : K) : ϕ.lift_normal E (algebraMap K E x) = algebraMap K E (ϕ x) :=
  @AlgHom.commutes K E E _ _ _ _ ((IsScalarTower.toAlgHom F K E).comp ϕ).toRingHom.toAlgebra _ x

@[simp]
theorem AlgHom.restrict_lift_normal [Normal F K] [Normal F E] : (ϕ.lift_normal E).restrictNormal K = ϕ :=
  AlgHom.ext fun x =>
    (algebraMap K E).Injective (Eq.trans (AlgHom.restrict_normal_commutes _ K x) (ϕ.lift_normal_commutes E x))

/--  If `E/K/F` is a tower of fields with `E/F` normal then we can lift
  an algebra isomorphism `ϕ : K ≃ₐ[F] K` to `ϕ.lift_normal E : E ≃ₐ[F] E`. -/
noncomputable def AlgEquiv.liftNormal [Normal F E] : E ≃ₐ[F] E :=
  AlgEquiv.ofBijective (χ.to_alg_hom.lift_normal E) (AlgHom.normal_bijective F E E _)

@[simp]
theorem AlgEquiv.lift_normal_commutes [Normal F E] (x : K) :
    χ.lift_normal E (algebraMap K E x) = algebraMap K E (χ x) :=
  χ.to_alg_hom.lift_normal_commutes E x

@[simp]
theorem AlgEquiv.restrict_lift_normal [Normal F K] [Normal F E] : (χ.lift_normal E).restrictNormal K = χ :=
  AlgEquiv.ext fun x =>
    (algebraMap K E).Injective (Eq.trans (AlgEquiv.restrict_normal_commutes _ K x) (χ.lift_normal_commutes E x))

theorem AlgEquiv.restrict_normal_hom_surjective [Normal F K] [Normal F E] :
    Function.Surjective (AlgEquiv.restrictNormalHom K : (E ≃ₐ[F] E) → K ≃ₐ[F] K) := fun χ =>
  ⟨χ.lift_normal E, χ.restrict_lift_normal E⟩

variable (F) (K) (E)

theorem is_solvable_of_is_scalar_tower [Normal F K] [h1 : IsSolvable (K ≃ₐ[F] K)] [h2 : IsSolvable (E ≃ₐ[K] E)] :
    IsSolvable (E ≃ₐ[F] E) := by
  let f : (E ≃ₐ[K] E) →* E ≃ₐ[F] E :=
    { toFun := fun ϕ =>
        AlgEquiv.ofAlgHom (ϕ.to_alg_hom.restrict_scalars F) (ϕ.symm.to_alg_hom.restrict_scalars F)
          (AlgHom.ext fun x => ϕ.apply_symm_apply x) (AlgHom.ext fun x => ϕ.symm_apply_apply x),
      map_one' := AlgEquiv.ext fun _ => rfl, map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  refine'
    solvable_of_ker_le_range f (AlgEquiv.restrictNormalHom K) fun ϕ hϕ =>
      ⟨{ ϕ with commutes' := fun x => _ }, AlgEquiv.ext fun _ => rfl⟩
  exact Eq.trans (ϕ.restrict_normal_commutes K x).symm (congr_argₓ _ (alg_equiv.ext_iff.mp hϕ x))

end lift

