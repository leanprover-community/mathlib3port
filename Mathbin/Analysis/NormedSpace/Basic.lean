import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.Algebra.Algebra.Subalgebra
import Mathbin.Analysis.Normed.Group.InfiniteSum
import Mathbin.Data.Matrix.Basic
import Mathbin.Topology.Algebra.Module
import Mathbin.Topology.Instances.Ennreal
import Mathbin.Topology.Sequences

/-!
# Normed spaces

In this file we define (semi)normed rings, fields, spaces, and algebras. We also prove some theorems
about these definitions.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

noncomputable section

open Filter Metric

open_locale TopologicalSpace BigOperators Nnreal Ennreal uniformity Pointwise

section SemiNormedRing

/--  A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class SemiNormedRing (α : Type _) extends HasNorm α, Ringₓ α, PseudoMetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a*b) ≤ norm a*norm b

/--  A normed ring is a ring endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class NormedRing (α : Type _) extends HasNorm α, Ringₓ α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a*b) ≤ norm a*norm b

/--  A normed ring is a seminormed ring. -/
instance (priority := 100) NormedRing.toSemiNormedRing [β : NormedRing α] : SemiNormedRing α :=
  { β with }

/--  A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class SemiNormedCommRing (α : Type _) extends SemiNormedRing α where
  mul_comm : ∀ x y : α, (x*y) = y*x

/--  A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class NormedCommRing (α : Type _) extends NormedRing α where
  mul_comm : ∀ x y : α, (x*y) = y*x

/--  A normed commutative ring is a seminormed commutative ring. -/
instance (priority := 100) NormedCommRing.toSemiNormedCommRing [β : NormedCommRing α] : SemiNormedCommRing α :=
  { β with }

instance : NormedCommRing PUnit :=
  { PUnit.normedGroup, PUnit.commRing with
    norm_mul := fun _ _ => by
      simp }

/--  A mixin class with the axiom `∥1∥ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class NormOneClass (α : Type _) [HasNorm α] [HasOne α] : Prop where
  norm_one : ∥(1 : α)∥ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

@[simp]
theorem nnnorm_one [SemiNormedGroup α] [HasOne α] [NormOneClass α] : ∥(1 : α)∥₊ = 1 :=
  Nnreal.eq norm_one

instance (priority := 100) SemiNormedCommRing.toCommRing [β : SemiNormedCommRing α] : CommRingₓ α :=
  { β with }

instance (priority := 100) NormedRing.toNormedGroup [β : NormedRing α] : NormedGroup α :=
  { β with }

instance (priority := 100) SemiNormedRing.toSemiNormedGroup [β : SemiNormedRing α] : SemiNormedGroup α :=
  { β with }

instance Prod.norm_one_class [NormedGroup α] [HasOne α] [NormOneClass α] [NormedGroup β] [HasOne β] [NormOneClass β] :
    NormOneClass (α × β) :=
  ⟨by
    simp [Prod.norm_def]⟩

variable [SemiNormedRing α]

theorem norm_mul_le (a b : α) : ∥a*b∥ ≤ ∥a∥*∥b∥ :=
  SemiNormedRing.norm_mul _ _

/--  A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.semiNormedRing {𝕜 : Type _} {_ : CommRingₓ 𝕜} {E : Type _} [SemiNormedRing E] {_ : Algebra 𝕜 E}
    (s : Subalgebra 𝕜 E) : SemiNormedRing s :=
  { s.to_submodule.semi_normed_group with norm_mul := fun a b => norm_mul_le a.1 b.1 }

/--  A subalgebra of a normed ring is also a normed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.normedRing {𝕜 : Type _} {_ : CommRingₓ 𝕜} {E : Type _} [NormedRing E] {_ : Algebra 𝕜 E}
    (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.semi_normed_ring with }

theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ∥l.prod∥ ≤ (l.map norm).Prod
  | [], h => (h rfl).elim
  | [a], _ => by
    simp
  | a :: b :: l, _ => by
    rw [List.map_cons, List.prod_cons, @List.prod_cons _ _ _ ∥a∥]
    refine' le_transₓ (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)

theorem List.norm_prod_le [NormOneClass α] : ∀ l : List α, ∥l.prod∥ ≤ (l.map norm).Prod
  | [] => by
    simp
  | a :: l => List.norm_prod_le' (List.cons_ne_nil a l)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Finset.norm_prod_le' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `NormedCommRing [`α]) "]")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder "(" [`hs] [":" `s.nonempty] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" `α)] [] ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥»
      "∥"
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i]))
      "∥")
     "≤"
     (Algebra.BigOperators.Basic.«term∏_in_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`i]) "∥")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `s)]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo
             (Tactic.rcasesPatMed
              [(Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])]
                "⟩")])
             [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_≠_» (Term.app `l.map [`f]) "≠" («term[_]» "[" [] "]")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])]))))))
        [])
       (group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.app `List.norm_prod_le' [`this])]) [])])))
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
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `s)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo
            (Tactic.rcasesPatMed
             [(Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])]
               "⟩")])
            [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_≠_» (Term.app `l.map [`f]) "≠" («term[_]» "[" [] "]")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])]))))))
       [])
      (group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.app `List.norm_prod_le' [`this])]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.app `List.norm_prod_le' [`this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `List.norm_prod_le' [`this])
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
  `List.norm_prod_le'
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
     [(Term.typeSpec ":" («term_≠_» (Term.app `l.map [`f]) "≠" («term[_]» "[" [] "]")))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] ["using" `hs]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_» (Term.app `l.map [`f]) "≠" («term[_]» "[" [] "]"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `l.map [`f])
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
  `l.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] `s)]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo
       (Tactic.rcasesPatMed
        [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])] "⟩")])
       [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl)]) [])]
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥»
    "∥"
    (Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i]))
    "∥")
   "≤"
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`i]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`i]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`i]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`i])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  Finset.norm_prod_le'
  { α : Type _ } [ NormedCommRing α ] ( s : Finset ι ) ( hs : s.nonempty ) ( f : ι → α )
    : ∥ ∏ i in s , f i ∥ ≤ ∏ i in s , ∥ f i ∥
  := by rcases s with ⟨ ⟨ l ⟩ , hl ⟩ have : l.map f ≠ [ ] := by simpa using hs simpa using List.norm_prod_le' this

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Finset.norm_prod_le [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `NormedCommRing [`α]) "]")
    (Term.instBinder "[" [] (Term.app `NormOneClass [`α]) "]")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" `α)] [] ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥»
      "∥"
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       " in "
       `s
       ", "
       (Term.app `f [`i]))
      "∥")
     "≤"
     (Algebra.BigOperators.Basic.«term∏_in_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`i]) "∥")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `s)]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo
             (Tactic.rcasesPatMed
              [(Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])]
                "⟩")])
             [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl)]) [])]
           "⟩")])
        [])
       (group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj (Term.app `l.map [`f]) "." `norm_prod_le)]) [])])))
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
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] `s)]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo
            (Tactic.rcasesPatMed
             [(Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])]
               "⟩")])
            [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl)]) [])]
          "⟩")])
       [])
      (group (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj (Term.app `l.map [`f]) "." `norm_prod_le)]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] ["using" (Term.proj (Term.app `l.map [`f]) "." `norm_prod_le)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `l.map [`f]) "." `norm_prod_le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `l.map [`f])
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
  `l.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `l.map [`f]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] `s)]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo
       (Tactic.rcasesPatMed
        [(Tactic.rcasesPat.tuple "⟨" [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])] "⟩")])
       [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hl)]) [])]
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥»
    "∥"
    (Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i]))
    "∥")
   "≤"
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`i]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`i]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`i]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`i])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  Finset.norm_prod_le
  { α : Type _ } [ NormedCommRing α ] [ NormOneClass α ] ( s : Finset ι ) ( f : ι → α )
    : ∥ ∏ i in s , f i ∥ ≤ ∏ i in s , ∥ f i ∥
  := by rcases s with ⟨ ⟨ l ⟩ , hl ⟩ simpa using l.map f . norm_prod_le

/--  If `α` is a seminormed ring, then `∥a^n∥≤ ∥a∥^n` for `n > 0`. See also `norm_pow_le`. -/
theorem norm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ∥a ^ n∥ ≤ ∥a∥ ^ n
  | 1, h => by
    simp
  | n+2, h => by
    rw [pow_succₓ _ (n+1), pow_succₓ _ (n+1)]
    exact
      le_transₓ (norm_mul_le a (a ^ n+1))
        (mul_le_mul (le_reflₓ _) (norm_pow_le' (Nat.succ_posₓ _)) (norm_nonneg _) (norm_nonneg _))

/--  If `α` is a seminormed ring with `∥1∥=1`, then `∥a^n∥≤ ∥a∥^n`. See also `norm_pow_le'`. -/
theorem norm_pow_le [NormOneClass α] (a : α) : ∀ n : ℕ, ∥a ^ n∥ ≤ ∥a∥ ^ n
  | 0 => by
    simp
  | n+1 => norm_pow_le' a n.zero_lt_succ

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `eventually_norm_pow_le [])
  (Command.declSig
   [(Term.explicitBinder "(" [`a] [":" `α] [] ")")]
   (Term.typeSpec
    ":"
    (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
     "∀ᶠ"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
     " in "
     `at_top
     ", "
     («term_≤_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_^_» `a "^" `n) "∥")
      "≤"
      («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `a "∥") "^" `n)))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj `eventually_at_top "." `mpr)
    [(Term.anonymousCtor
      "⟨"
      [(numLit "1")
       ","
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`b `h] [])]
         "=>"
         (Term.app `norm_pow_le' [`a (Term.app (Term.proj `Nat.succ_le_iff "." `mp) [`h])])))]
      "⟩")])
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
   (Term.proj `eventually_at_top "." `mpr)
   [(Term.anonymousCtor
     "⟨"
     [(numLit "1")
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`b `h] [])]
        "=>"
        (Term.app `norm_pow_le' [`a (Term.app (Term.proj `Nat.succ_le_iff "." `mp) [`h])])))]
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
   [(numLit "1")
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`b `h] [])]
      "=>"
      (Term.app `norm_pow_le' [`a (Term.app (Term.proj `Nat.succ_le_iff "." `mp) [`h])])))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`b `h] [])]
    "=>"
    (Term.app `norm_pow_le' [`a (Term.app (Term.proj `Nat.succ_le_iff "." `mp) [`h])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_pow_le' [`a (Term.app (Term.proj `Nat.succ_le_iff "." `mp) [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `Nat.succ_le_iff "." `mp) [`h])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Nat.succ_le_iff "." `mp)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Nat.succ_le_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `Nat.succ_le_iff "." `mp) [`h]) []]
 ")")
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
  `norm_pow_le'
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `eventually_at_top "." `mpr)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `eventually_at_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
   " in "
   `at_top
   ", "
   («term_≤_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_^_» `a "^" `n) "∥")
    "≤"
    («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `a "∥") "^" `n)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_^_» `a "^" `n) "∥")
   "≤"
   («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `a "∥") "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `a "∥") "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `a "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_^_» `a "^" `n) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» `a "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `at_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  eventually_norm_pow_le
  ( a : α ) : ∀ᶠ n : ℕ in at_top , ∥ a ^ n ∥ ≤ ∥ a ∥ ^ n
  := eventually_at_top . mpr ⟨ 1 , fun b h => norm_pow_le' a Nat.succ_le_iff . mp h ⟩

/--  In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
theorem mul_left_bound (x : α) : ∀ y : α, ∥AddMonoidHom.mulLeft x y∥ ≤ ∥x∥*∥y∥ :=
  norm_mul_le x

/--  In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
theorem mul_right_bound (x : α) : ∀ y : α, ∥AddMonoidHom.mulRight x y∥ ≤ ∥x∥*∥y∥ := fun y => by
  rw [mul_commₓ]
  convert norm_mul_le y x

/--  Seminormed ring structure on the product of two seminormed rings, using the sup norm. -/
instance Prod.semiNormedRing [SemiNormedRing β] : SemiNormedRing (α × β) :=
  { Prod.semiNormedGroup with
    norm_mul := fun x y =>
      calc ∥x*y∥ = ∥(x.1*y.1, x.2*y.2)∥ := rfl
        _ = max ∥x.1*y.1∥ ∥x.2*y.2∥ := rfl
        _ ≤ max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥) := max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2)
        _ = max (∥x.1∥*∥y.1∥) (∥y.2∥*∥x.2∥) := by
        simp [mul_commₓ]
        _ ≤ max ∥x.1∥ ∥x.2∥*max ∥y.2∥ ∥y.1∥ := by
        apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
        _ = max ∥x.1∥ ∥x.2∥*max ∥y.1∥ ∥y.2∥ := by
        simp [max_commₓ]
        _ = ∥x∥*∥y∥ := rfl
         }

/--  Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def Matrix.semiNormedGroup {n m : Type _} [Fintype n] [Fintype m] : SemiNormedGroup (Matrix n m α) :=
  Pi.semiNormedGroup

attribute [local instance] Matrix.semiNormedGroup

theorem semi_norm_matrix_le_iff {n m : Type _} [Fintype n] [Fintype m] {r : ℝ} (hr : 0 ≤ r) {A : Matrix n m α} :
    ∥A∥ ≤ r ↔ ∀ i j, ∥A i j∥ ≤ r := by
  simp [pi_semi_norm_le_iff hr]

end SemiNormedRing

section NormedRing

variable [NormedRing α]

theorem Units.norm_pos [Nontrivial α] (x : Units α) : 0 < ∥(x : α)∥ :=
  norm_pos_iff.mpr (Units.ne_zero x)

/--  Normed ring structure on the product of two normed rings, using the sup norm. -/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { Prod.semiNormedGroup with norm_mul := norm_mul_le }

/--  Normed group instance (using sup norm of sup norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def Matrix.normedGroup {n m : Type _} [Fintype n] [Fintype m] : NormedGroup (Matrix n m α) :=
  Pi.normedGroup

end NormedRing

instance (priority := 100) semi_normed_ring_top_monoid [SemiNormedRing α] : HasContinuousMul α :=
  ⟨continuous_iff_continuous_at.2 $ fun x =>
      tendsto_iff_norm_tendsto_zero.2 $ by
        have : ∀ e : α × α, ∥(e.1*e.2) - x.1*x.2∥ ≤ (∥e.1∥*∥e.2 - x.2∥)+∥e.1 - x.1∥*∥x.2∥ := by
          intro e
          calc ∥(e.1*e.2) - x.1*x.2∥ ≤ ∥(e.1*e.2 - x.2)+(e.1 - x.1)*x.2∥ := by
            rw [mul_sub, sub_mul, sub_add_sub_cancel]_ ≤ (∥e.1∥*∥e.2 - x.2∥)+∥e.1 - x.1∥*∥x.2∥ :=
            norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
        refine' squeeze_zero (fun e => norm_nonneg _) this _
        convert
          ((continuous_fst.tendsto x).norm.mul ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)
        show tendsto _ _ _
        exact tendsto_const_nhds
        simp ⟩

/--  A seminormed ring is a topological ring. -/
instance (priority := 100) semi_normed_top_ring [SemiNormedRing α] : TopologicalRing α :=
  {  }

/--  A normed field is a field with a norm satisfying ∥x y∥ = ∥x∥ ∥y∥. -/
class NormedField (α : Type _) extends HasNorm α, Field α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a*b) = norm a*norm b

/--  A nondiscrete normed field is a normed field in which there is an element of norm different from
`0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by multiplication
by the powers of any element, and thus to relate algebra and topology. -/
class NondiscreteNormedField (α : Type _) extends NormedField α where
  non_trivial : ∃ x : α, 1 < ∥x∥

namespace NormedField

section NormedField

variable [NormedField α]

@[simp]
theorem norm_mul (a b : α) : ∥a*b∥ = ∥a∥*∥b∥ :=
  NormedField.norm_mul' a b

instance (priority := 100) to_normed_comm_ring : NormedCommRing α :=
  { ‹NormedField α› with norm_mul := fun a b => (norm_mul a b).le }

instance (priority := 900) to_norm_one_class : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (@one_ne_zero α _ _)) $ by
      rw [← norm_mul, mul_oneₓ, mul_oneₓ]⟩

@[simp]
theorem nnnorm_mul (a b : α) : ∥a*b∥₊ = ∥a∥₊*∥b∥₊ :=
  Nnreal.eq $ norm_mul a b

/--  `norm` as a `monoid_hom`. -/
@[simps]
def norm_hom : MonoidWithZeroHom α ℝ :=
  ⟨norm, norm_zero, norm_one, norm_mul⟩

/--  `nnnorm` as a `monoid_hom`. -/
@[simps]
def nnnorm_hom : MonoidWithZeroHom α ℝ≥0 :=
  ⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩

@[simp]
theorem norm_pow (a : α) : ∀ n : ℕ, ∥a ^ n∥ = ∥a∥ ^ n :=
  (norm_hom.toMonoidHom : α →* ℝ).map_pow a

@[simp]
theorem nnnorm_pow (a : α) (n : ℕ) : ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
  (nnnorm_hom.toMonoidHom : α →* ℝ≥0 ).map_pow a n

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
  (Command.declId `norm_prod [])
  (Command.declSig
   [(Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`β])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `β "→" `α)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Analysis.Normed.Group.Basic.«term∥_∥»
      "∥"
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
       " in "
       `s
       ", "
       (Term.app `f [`b]))
      "∥")
     "="
     (Algebra.BigOperators.Basic.«term∏_in_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
      " in "
      `s
      ", "
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`b]) "∥")))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj
     (Term.paren
      "("
      [(Term.proj `norm_hom "." `toMonoidHom)
       [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Basic.termℝ "ℝ")))]]
      ")")
     "."
     `map_prod)
    [`f `s])
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
   (Term.proj
    (Term.paren
     "("
     [(Term.proj `norm_hom "." `toMonoidHom)
      [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Basic.termℝ "ℝ")))]]
     ")")
    "."
    `map_prod)
   [`f `s])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.paren
    "("
    [(Term.proj `norm_hom "." `toMonoidHom)
     [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Basic.termℝ "ℝ")))]]
    ")")
   "."
   `map_prod)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren
   "("
   [(Term.proj `norm_hom "." `toMonoidHom)
    [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Basic.termℝ "ℝ")))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Basic.termℝ "ℝ"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Hom.«term_→*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.proj `norm_hom "." `toMonoidHom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `norm_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Analysis.Normed.Group.Basic.«term∥_∥»
    "∥"
    (Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
     " in "
     `s
     ", "
     (Term.app `f [`b]))
    "∥")
   "="
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
    " in "
    `s
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`b]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
   " in "
   `s
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`b]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`b]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`b])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    norm_prod
    ( s : Finset β ) ( f : β → α ) : ∥ ∏ b in s , f b ∥ = ∏ b in s , ∥ f b ∥
    := ( norm_hom . toMonoidHom : α →* ℝ ) . map_prod f s

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
  (Command.declId `nnnorm_prod [])
  (Command.declSig
   [(Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`β])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `β "→" `α)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Analysis.Normed.Group.Basic.«term∥_∥₊»
      "∥"
      (Algebra.BigOperators.Basic.«term∏_in_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
       " in "
       `s
       ", "
       (Term.app `f [`b]))
      "∥₊")
     "="
     (Algebra.BigOperators.Basic.«term∏_in_,_»
      "∏"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
      " in "
      `s
      ", "
      (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `f [`b]) "∥₊")))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj
     (Term.paren
      "("
      [(Term.proj `nnnorm_hom "." `toMonoidHom)
       [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ")))]]
      ")")
     "."
     `map_prod)
    [`f `s])
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
   (Term.proj
    (Term.paren
     "("
     [(Term.proj `nnnorm_hom "." `toMonoidHom)
      [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ")))]]
     ")")
    "."
    `map_prod)
   [`f `s])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.paren
    "("
    [(Term.proj `nnnorm_hom "." `toMonoidHom)
     [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ")))]]
    ")")
   "."
   `map_prod)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren
   "("
   [(Term.proj `nnnorm_hom "." `toMonoidHom)
    [(Term.typeAscription ":" (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ")))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Hom.«term_→*_» `α " →* " (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 "))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Hom.«term_→*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Nnreal.«termℝ≥0»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.proj `nnnorm_hom "." `toMonoidHom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `nnnorm_hom
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Analysis.Normed.Group.Basic.«term∥_∥₊»
    "∥"
    (Algebra.BigOperators.Basic.«term∏_in_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
     " in "
     `s
     ", "
     (Term.app `f [`b]))
    "∥₊")
   "="
   (Algebra.BigOperators.Basic.«term∏_in_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
    " in "
    `s
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `f [`b]) "∥₊")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_in_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] []))
   " in "
   `s
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `f [`b]) "∥₊"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `f [`b]) "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`b])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    nnnorm_prod
    ( s : Finset β ) ( f : β → α ) : ∥ ∏ b in s , f b ∥₊ = ∏ b in s , ∥ f b ∥₊
    := ( nnnorm_hom . toMonoidHom : α →* ℝ≥0 ) . map_prod f s

@[simp]
theorem norm_div (a b : α) : ∥a / b∥ = ∥a∥ / ∥b∥ :=
  (norm_hom : MonoidWithZeroHom α ℝ).map_div a b

@[simp]
theorem nnnorm_div (a b : α) : ∥a / b∥₊ = ∥a∥₊ / ∥b∥₊ :=
  (nnnorm_hom : MonoidWithZeroHom α ℝ≥0 ).map_div a b

@[simp]
theorem norm_inv (a : α) : ∥a⁻¹∥ = ∥a∥⁻¹ :=
  (norm_hom : MonoidWithZeroHom α ℝ).map_inv a

@[simp]
theorem nnnorm_inv (a : α) : ∥a⁻¹∥₊ = ∥a∥₊⁻¹ :=
  Nnreal.eq $ by
    simp

@[simp]
theorem norm_zpow : ∀ a : α n : ℤ, ∥a ^ n∥ = ∥a∥ ^ n :=
  (norm_hom : MonoidWithZeroHom α ℝ).map_zpow

@[simp]
theorem nnnorm_zpow : ∀ a : α n : ℤ, ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
  (nnnorm_hom : MonoidWithZeroHom α ℝ≥0 ).map_zpow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.instance
  (Term.attrKind [])
  "instance"
  [(Command.namedPrio "(" "priority" ":=" (numLit "100") ")")]
  []
  (Command.declSig [] (Term.typeSpec ":" (Term.app `HasContinuousInv₀ [`α])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`r `r0] [])]
             "=>"
             (Term.app (Term.proj `tendsto_iff_norm_tendsto_zero "." (fieldIdx "2")) [(Term.hole "_")])))]
          "⟩"))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`r0' []]
           [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥")))]
           ":="
           (Term.app (Term.proj `norm_pos_iff "." (fieldIdx "2")) [`r0]))))
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `exists_between [`r0']))]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε0)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `εr)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
              "∀ᶠ"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
              " in "
              (Term.app (Topology.Basic.term𝓝 "𝓝") [`r])
              ", "
              («term_≤_»
               (Analysis.Normed.Group.Basic.«term∥_∥»
                "∥"
                («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
                "∥")
               "≤"
               («term_/_»
                («term_/_»
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
                 "/"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
                "/"
                `ε))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.filterUpwards
                 "filter_upwards"
                 "["
                 [(Term.app
                   (Term.proj (Term.app `is_open_lt [`continuous_const `continuous_norm]) "." `eventually_mem)
                   [`εr])]
                 "]"
                 [])
                [])
               (group (Tactic.intro "intro" [`e `he]) [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`e0 []]
                   [(Term.typeSpec ":" («term_≠_» `e "≠" (numLit "0")))]
                   ":="
                   (Term.app (Term.proj `norm_pos_iff "." (fieldIdx "1")) [(Term.app `ε0.trans [`he])]))))
                [])
               (group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_=_»
                    (Analysis.Normed.Group.Basic.«term∥_∥»
                     "∥"
                     («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
                     "∥")
                    "="
                    («term_/_»
                     («term_/_»
                      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
                      "/"
                      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
                     "/"
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `mul_commₓ)] "]"] [] [])
                        [])]))))
                  (calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    («term_/_»
                     («term_/_»
                      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
                      "/"
                      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
                     "/"
                     `ε))
                   ":="
                   (Term.app
                    `div_le_div_of_le_left
                    [(Term.app
                      `div_nonneg
                      [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
                     `ε0
                     `he.le]))])
                [])]))))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `squeeze_zero'
          [(«term_$__»
            `eventually_of_forall
            "$"
            (Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")]))))
           `this
           (Term.hole "_")]))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.proj
            (Term.proj (Term.proj (Term.app `continuous_const.sub [`continuous_id]) "." `norm) "." `div_const)
            "."
            `div_const)
           "."
           `tendsto')
          [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
        [])
       (group (Tactic.simp "simp" [] [] [] []) [])])))
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
     [(group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`r `r0] [])]
            "=>"
            (Term.app (Term.proj `tendsto_iff_norm_tendsto_zero "." (fieldIdx "2")) [(Term.hole "_")])))]
         "⟩"))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`r0' []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥")))]
          ":="
          (Term.app (Term.proj `norm_pos_iff "." (fieldIdx "2")) [`r0]))))
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `exists_between [`r0']))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε0)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `εr)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
             "∀ᶠ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
             " in "
             (Term.app (Topology.Basic.term𝓝 "𝓝") [`r])
             ", "
             («term_≤_»
              (Analysis.Normed.Group.Basic.«term∥_∥»
               "∥"
               («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
               "∥")
              "≤"
              («term_/_»
               («term_/_»
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
                "/"
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
               "/"
               `ε))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.filterUpwards
                "filter_upwards"
                "["
                [(Term.app
                  (Term.proj (Term.app `is_open_lt [`continuous_const `continuous_norm]) "." `eventually_mem)
                  [`εr])]
                "]"
                [])
               [])
              (group (Tactic.intro "intro" [`e `he]) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`e0 []]
                  [(Term.typeSpec ":" («term_≠_» `e "≠" (numLit "0")))]
                  ":="
                  (Term.app (Term.proj `norm_pos_iff "." (fieldIdx "1")) [(Term.app `ε0.trans [`he])]))))
               [])
              (group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_=_»
                   (Analysis.Normed.Group.Basic.«term∥_∥»
                    "∥"
                    («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
                    "∥")
                   "="
                   («term_/_»
                    («term_/_»
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
                     "/"
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
                    "/"
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `mul_commₓ)] "]"] [] [])
                       [])]))))
                 (calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_/_»
                    («term_/_»
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
                     "/"
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
                    "/"
                    `ε))
                  ":="
                  (Term.app
                   `div_le_div_of_le_left
                   [(Term.app
                     `div_nonneg
                     [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
                    `ε0
                    `he.le]))])
               [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `squeeze_zero'
         [(«term_$__»
           `eventually_of_forall
           "$"
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")]))))
          `this
          (Term.hole "_")]))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          (Term.proj
           (Term.proj (Term.proj (Term.app `continuous_const.sub [`continuous_id]) "." `norm) "." `div_const)
           "."
           `div_const)
          "."
          `tendsto')
         [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
       [])
      (group (Tactic.simp "simp" [] [] [] []) [])])))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj
     (Term.proj
      (Term.proj (Term.proj (Term.app `continuous_const.sub [`continuous_id]) "." `norm) "." `div_const)
      "."
      `div_const)
     "."
     `tendsto')
    [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.proj
     (Term.proj (Term.proj (Term.app `continuous_const.sub [`continuous_id]) "." `norm) "." `div_const)
     "."
     `div_const)
    "."
    `tendsto')
   [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
  (Term.proj
   (Term.proj
    (Term.proj (Term.proj (Term.app `continuous_const.sub [`continuous_id]) "." `norm) "." `div_const)
    "."
    `div_const)
   "."
   `tendsto')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj
   (Term.proj (Term.proj (Term.app `continuous_const.sub [`continuous_id]) "." `norm) "." `div_const)
   "."
   `div_const)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj (Term.app `continuous_const.sub [`continuous_id]) "." `norm) "." `div_const)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `continuous_const.sub [`continuous_id]) "." `norm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `continuous_const.sub [`continuous_id])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `continuous_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_const.sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `continuous_const.sub [`continuous_id]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `squeeze_zero'
    [(«term_$__»
      `eventually_of_forall
      "$"
      (Term.fun
       "fun"
       (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")]))))
     `this
     (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `squeeze_zero'
   [(«term_$__»
     `eventually_of_forall
     "$"
     (Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")]))))
    `this
    (Term.hole "_")])
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
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_$__»
   `eventually_of_forall
   "$"
   (Term.fun
    "fun"
    (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_nonneg [(Term.hole "_")])
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
  `norm_nonneg
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `eventually_of_forall
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__»
   `eventually_of_forall
   "$"
   (Term.fun
    "fun"
    (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")]))))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `squeeze_zero'
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
       (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
        "∀ᶠ"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
        " in "
        (Term.app (Topology.Basic.term𝓝 "𝓝") [`r])
        ", "
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term∥_∥»
          "∥"
          («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
          "∥")
         "≤"
         («term_/_»
          («term_/_»
           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
           "/"
           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
          "/"
          `ε))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.filterUpwards
           "filter_upwards"
           "["
           [(Term.app
             (Term.proj (Term.app `is_open_lt [`continuous_const `continuous_norm]) "." `eventually_mem)
             [`εr])]
           "]"
           [])
          [])
         (group (Tactic.intro "intro" [`e `he]) [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`e0 []]
             [(Term.typeSpec ":" («term_≠_» `e "≠" (numLit "0")))]
             ":="
             (Term.app (Term.proj `norm_pos_iff "." (fieldIdx "1")) [(Term.app `ε0.trans [`he])]))))
          [])
         (group
          (tacticCalc_
           "calc"
           [(calcStep
             («term_=_»
              (Analysis.Normed.Group.Basic.«term∥_∥»
               "∥"
               («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
               "∥")
              "="
              («term_/_»
               («term_/_»
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
                "/"
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
               "/"
               (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `mul_commₓ)] "]"] [] [])
                  [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_/_»
               («term_/_»
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
                "/"
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
               "/"
               `ε))
             ":="
             (Term.app
              `div_le_div_of_le_left
              [(Term.app
                `div_nonneg
                [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
               `ε0
               `he.le]))])
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
       (Tactic.filterUpwards
        "filter_upwards"
        "["
        [(Term.app (Term.proj (Term.app `is_open_lt [`continuous_const `continuous_norm]) "." `eventually_mem) [`εr])]
        "]"
        [])
       [])
      (group (Tactic.intro "intro" [`e `he]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`e0 []]
          [(Term.typeSpec ":" («term_≠_» `e "≠" (numLit "0")))]
          ":="
          (Term.app (Term.proj `norm_pos_iff "." (fieldIdx "1")) [(Term.app `ε0.trans [`he])]))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
            "∥")
           "="
           («term_/_»
            («term_/_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
             "/"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
            "/"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `mul_commₓ)] "]"] [] [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           («term_/_»
            («term_/_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
             "/"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
            "/"
            `ε))
          ":="
          (Term.app
           `div_le_div_of_le_left
           [(Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
            `ε0
            `he.le]))])
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
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
       "∥")
      "="
      («term_/_»
       («term_/_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
        "/"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
       "/"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `mul_commₓ)] "]"] [] []) [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      («term_/_»
       («term_/_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
        "/"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
       "/"
       `ε))
     ":="
     (Term.app
      `div_le_div_of_le_left
      [(Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
       `ε0
       `he.le]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `div_le_div_of_le_left
   [(Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
    `ε0
    `he.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `he.le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ε0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_nonneg [(Term.hole "_")])
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
  `norm_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `norm_nonneg [(Term.hole "_")])
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
  `norm_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `div_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `div_nonneg
   [(Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
    (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `div_le_div_of_le_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   («term_/_»
    («term_/_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
     "/"
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
    "/"
    `ε))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   («term_/_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
    "/"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
   "/"
   `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  («term_/_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
   "/"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `r "-" `e)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `mul_commₓ)] "]"] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `mul_commₓ)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.fieldSimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Analysis.Normed.Group.Basic.«term∥_∥»
    "∥"
    («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
    "∥")
   "="
   («term_/_»
    («term_/_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
     "/"
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
    "/"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   («term_/_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
    "/"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
   "/"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  («term_/_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
   "/"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `r "-" `e)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥»
   "∥"
   («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
   "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_⁻¹» `r "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Init.Logic.«term_⁻¹» `e "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`e0 []]
     [(Term.typeSpec ":" («term_≠_» `e "≠" (numLit "0")))]
     ":="
     (Term.app (Term.proj `norm_pos_iff "." (fieldIdx "1")) [(Term.app `ε0.trans [`he])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `norm_pos_iff "." (fieldIdx "1")) [(Term.app `ε0.trans [`he])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ε0.trans [`he])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `he
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ε0.trans
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `ε0.trans [`he]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `norm_pos_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `norm_pos_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≠_» `e "≠" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`e `he])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `he
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.filterUpwards
   "filter_upwards"
   "["
   [(Term.app (Term.proj (Term.app `is_open_lt [`continuous_const `continuous_norm]) "." `eventually_mem) [`εr])]
   "]"
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.filterUpwards', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `is_open_lt [`continuous_const `continuous_norm]) "." `eventually_mem) [`εr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `εr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `is_open_lt [`continuous_const `continuous_norm]) "." `eventually_mem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `is_open_lt [`continuous_const `continuous_norm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `continuous_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `continuous_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_open_lt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `is_open_lt [`continuous_const `continuous_norm]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
   " in "
   (Term.app (Topology.Basic.term𝓝 "𝓝") [`r])
   ", "
   («term_≤_»
    (Analysis.Normed.Group.Basic.«term∥_∥»
     "∥"
     («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
     "∥")
    "≤"
    («term_/_»
     («term_/_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
      "/"
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
     "/"
     `ε)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥»
    "∥"
    («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
    "∥")
   "≤"
   («term_/_»
    («term_/_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
     "/"
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
    "/"
    `ε))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   («term_/_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
    "/"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
   "/"
   `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  («term_/_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
   "/"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `r "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» `r "-" `e) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `r "-" `e)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥»
   "∥"
   («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
   "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (Init.Logic.«term_⁻¹» `e "⁻¹") "-" (Init.Logic.«term_⁻¹» `r "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_⁻¹» `r "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Init.Logic.«term_⁻¹» `e "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [`r])
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
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
instance
  ( priority := 100 )
  : HasContinuousInv₀ α
  :=
    by
      refine' ⟨ fun r r0 => tendsto_iff_norm_tendsto_zero . 2 _ ⟩
        have r0' : 0 < ∥ r ∥ := norm_pos_iff . 2 r0
        rcases exists_between r0' with ⟨ ε , ε0 , εr ⟩
        have
          : ∀ᶠ e in 𝓝 r , ∥ e ⁻¹ - r ⁻¹ ∥ ≤ ∥ r - e ∥ / ∥ r ∥ / ε
            :=
            by
              filter_upwards [ is_open_lt continuous_const continuous_norm . eventually_mem εr ]
                intro e he
                have e0 : e ≠ 0 := norm_pos_iff . 1 ε0.trans he
                calc
                  ∥ e ⁻¹ - r ⁻¹ ∥ = ∥ r - e ∥ / ∥ r ∥ / ∥ e ∥ := by field_simp [ mul_commₓ ]
                    _ ≤ ∥ r - e ∥ / ∥ r ∥ / ε := div_le_div_of_le_left div_nonneg norm_nonneg _ norm_nonneg _ ε0 he.le
        refine' squeeze_zero' eventually_of_forall $ fun _ => norm_nonneg _ this _
        refine' continuous_const.sub continuous_id . norm . div_const . div_const . tendsto' _ _ _
        simp

end NormedField

variable (α) [NondiscreteNormedField α]

theorem exists_one_lt_norm : ∃ x : α, 1 < ∥x∥ :=
  ‹NondiscreteNormedField α›.non_trivial

theorem exists_norm_lt_one : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < 1 := by
  rcases exists_one_lt_norm α with ⟨y, hy⟩
  refine' ⟨y⁻¹, _, _⟩
  ·
    simp only [inv_eq_zero, Ne.def, norm_pos_iff]
    rintro rfl
    rw [norm_zero] at hy
    exact lt_asymmₓ zero_lt_one hy
  ·
    simp [inv_lt_one hy]

theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ∥x∥ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by
    rwa [norm_pow]⟩

theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < r :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hle, hlt⟩ := exists_mem_Ioc_zpow hr hw
  ⟨w ^ n, by
    rw [norm_zpow] <;> exact zpow_pos_of_pos (lt_transₓ zero_lt_one hw) _, by
    rwa [norm_zpow]⟩

variable {α}

@[instance]
theorem punctured_nhds_ne_bot (x : α) : ne_bot (𝓝[≠] x) := by
  rw [← mem_closure_iff_nhds_within_ne_bot, Metric.mem_closure_iff]
  rintro ε ε0
  rcases NormedField.exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
  refine' ⟨x+b, mt (set.mem_singleton_iff.trans add_right_eq_selfₓ).1 $ norm_pos_iff.1 hb0, _⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel']

@[instance]
theorem nhds_within_is_unit_ne_bot : ne_bot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [is_unit_iff_ne_zero] using punctured_nhds_ne_bot (0 : α)

end NormedField

instance : NormedField ℝ :=
  { Real.normedGroup with norm_mul' := abs_mul }

instance : NondiscreteNormedField ℝ where
  non_trivial :=
    ⟨2, by
      unfold norm
      rw [abs_of_nonneg] <;> norm_num⟩

namespace Real

theorem norm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥ = x :=
  abs_of_nonneg hx

theorem norm_of_nonpos {x : ℝ} (hx : x ≤ 0) : ∥x∥ = -x :=
  abs_of_nonpos hx

@[simp]
theorem norm_coe_nat (n : ℕ) : ∥(n : ℝ)∥ = n :=
  abs_of_nonneg n.cast_nonneg

@[simp]
theorem nnnorm_coe_nat (n : ℕ) : ∥(n : ℝ)∥₊ = n :=
  Nnreal.eq $ by
    simp

@[simp]
theorem norm_two : ∥(2 : ℝ)∥ = 2 :=
  abs_of_pos (@zero_lt_two ℝ _ _)

@[simp]
theorem nnnorm_two : ∥(2 : ℝ)∥₊ = 2 :=
  Nnreal.eq $ by
    simp

theorem nnnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥₊ = ⟨x, hx⟩ :=
  Nnreal.eq $ norm_of_nonneg hx

theorem ennnorm_eq_of_real {x : ℝ} (hx : 0 ≤ x) : (∥x∥₊ : ℝ≥0∞) = Ennreal.ofReal x := by
  rw [← of_real_norm_eq_coe_nnnorm, norm_of_nonneg hx]

theorem of_real_le_ennnorm (x : ℝ) : Ennreal.ofReal x ≤ ∥x∥₊ := by
  by_cases' hx : 0 ≤ x
  ·
    rw [Real.ennnorm_eq_of_real hx]
    rfl'
  ·
    rw [Ennreal.of_real_eq_zero.2 (le_of_ltₓ (not_leₓ.1 hx))]
    exact bot_le

/--  If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `module.punctured_nhds_ne_bot`. -/
instance punctured_nhds_module_ne_bot {E : Type _} [AddCommGroupₓ E] [TopologicalSpace E] [HasContinuousAdd E]
    [Nontrivial E] [Module ℝ E] [HasContinuousSmul ℝ E] (x : E) : ne_bot (𝓝[≠] x) :=
  Module.punctured_nhds_ne_bot ℝ E x

end Real

namespace Nnreal

open_locale Nnreal

@[simp]
theorem norm_eq (x : ℝ≥0 ) : ∥(x : ℝ)∥ = x := by
  rw [Real.norm_eq_abs, x.abs_eq]

@[simp]
theorem nnnorm_eq (x : ℝ≥0 ) : ∥(x : ℝ)∥₊ = x :=
  Nnreal.eq $ Real.norm_of_nonneg x.2

end Nnreal

@[simp]
theorem norm_norm [SemiNormedGroup α] (x : α) : ∥∥x∥∥ = ∥x∥ :=
  Real.norm_of_nonneg (norm_nonneg _)

@[simp]
theorem nnnorm_norm [SemiNormedGroup α] (a : α) : ∥∥a∥∥₊ = ∥a∥₊ := by
  simpa [Real.nnnorm_of_nonneg (norm_nonneg a)]

/--  A restatement of `metric_space.tendsto_at_top` in terms of the norm. -/
theorem NormedGroup.tendsto_at_top [Nonempty α] [SemilatticeSup α] {β : Type _} [SemiNormedGroup β] {f : α → β}
    {b : β} : tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ∥f n - b∥ < ε :=
  (at_top_basis.tendsto_iff Metric.nhds_basis_ball).trans
    (by
      simp [dist_eq_norm])

/-- 
A variant of `normed_group.tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedGroup.tendsto_at_top' [Nonempty α] [SemilatticeSup α] [NoTopOrder α] {β : Type _} [SemiNormedGroup β]
    {f : α → β} {b : β} : tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ∥f n - b∥ < ε :=
  (at_top_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans
    (by
      simp [dist_eq_norm])

-- failed to format: format: uncaught backtrack exception
instance
  : NormedCommRing ℤ
  where
    norm n := ∥ ( n : ℝ ) ∥
      norm_mul m n := le_of_eqₓ $ by simp only [ norm , Int.cast_mul , abs_mul ]
      dist_eq m n := by simp only [ Int.dist_eq , norm , Int.cast_sub ]
      mul_comm := mul_commₓ

@[norm_cast]
theorem Int.norm_cast_real (m : ℤ) : ∥(m : ℝ)∥ = ∥m∥ :=
  rfl

theorem Int.norm_eq_abs (n : ℤ) : ∥n∥ = |n| :=
  rfl

theorem Nnreal.coe_nat_abs (n : ℤ) : (n.nat_abs : ℝ≥0 ) = ∥n∥₊ :=
  Nnreal.eq $
    calc ((n.nat_abs : ℝ≥0 ) : ℝ) = (n.nat_abs : ℤ) := by
      simp only [Int.cast_coe_nat, Nnreal.coe_nat_cast]
      _ = |n| := by
      simp only [← Int.abs_eq_nat_abs, Int.cast_abs]
      _ = ∥n∥ := rfl
      

instance : NormOneClass ℤ :=
  ⟨by
    simp [← Int.norm_cast_real]⟩

-- failed to format: format: uncaught backtrack exception
instance
  : NormedField ℚ
  where
    norm r := ∥ ( r : ℝ ) ∥
      norm_mul' r₁ r₂ := by simp only [ norm , Rat.cast_mul , abs_mul ]
      dist_eq r₁ r₂ := by simp only [ Rat.dist_eq , norm , Rat.cast_sub ]

instance : NondiscreteNormedField ℚ where
  non_trivial :=
    ⟨2, by
      unfold norm
      rw [abs_of_nonneg] <;> norm_num⟩

@[norm_cast, simp]
theorem Rat.norm_cast_real (r : ℚ) : ∥(r : ℝ)∥ = ∥r∥ :=
  rfl

@[norm_cast, simp]
theorem Int.norm_cast_rat (m : ℤ) : ∥(m : ℚ)∥ = ∥m∥ := by
  rw [← Rat.norm_cast_real, ← Int.norm_cast_real] <;> congr 1 <;> norm_cast

section

variable [SemiNormedGroup α]

theorem norm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥ ≤ n*∥a∥ := by
  induction' n with n ih
  ·
    simp only [norm_zero, Nat.cast_zero, zero_mul, zero_smul]
  simp only [Nat.succ_eq_add_one, add_smul, add_mulₓ, one_mulₓ, Nat.cast_add, Nat.cast_one, one_nsmul]
  exact norm_add_le_of_le ih le_rfl

theorem norm_zsmul_le (n : ℤ) (a : α) : ∥n • a∥ ≤ ∥n∥*∥a∥ := by
  induction' n with n n
  ·
    simp only [Int.of_nat_eq_coe, coe_nat_zsmul]
    convert norm_nsmul_le n a
    exact Nat.abs_cast n
  ·
    simp only [Int.neg_succ_of_nat_coe, neg_smul, norm_neg, coe_nat_zsmul]
    convert norm_nsmul_le n.succ a
    exact Nat.abs_cast n.succ

theorem nnnorm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥₊ ≤ n*∥a∥₊ := by
  simpa only [← Nnreal.coe_le_coe, Nnreal.coe_mul, Nnreal.coe_nat_cast] using norm_nsmul_le n a

theorem nnnorm_zsmul_le (n : ℤ) (a : α) : ∥n • a∥₊ ≤ ∥n∥₊*∥a∥₊ := by
  simpa only [← Nnreal.coe_le_coe, Nnreal.coe_mul] using norm_zsmul_le n a

end

section SemiNormedSpace

section Prio

-- ././Mathport/Syntax/Translate/Basic.lean:169:9: warning: unsupported option extends_priority
set_option extends_priority 920

/--  A seminormed space over a normed field is a vector space endowed with a seminorm which satisfies
the equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class SemiNormedSpace (α : Type _) (β : Type _) [NormedField α] [SemiNormedGroup β] extends Module α β where
  norm_smul_le : ∀ a : α b : β, ∥a • b∥ ≤ ∥a∥*∥b∥

-- ././Mathport/Syntax/Translate/Basic.lean:169:9: warning: unsupported option extends_priority
set_option extends_priority 920

/--  A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class NormedSpace (α : Type _) (β : Type _) [NormedField α] [NormedGroup β] extends Module α β where
  norm_smul_le : ∀ a : α b : β, ∥a • b∥ ≤ ∥a∥*∥b∥

/--  A normed space is a seminormed space. -/
instance (priority := 100) NormedSpace.toSemiNormedSpace [NormedField α] [NormedGroup β] [γ : NormedSpace α β] :
    SemiNormedSpace α β :=
  { γ with }

end Prio

variable [NormedField α] [SemiNormedGroup β]

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  SemiNormedSpace.has_bounded_smul
  [ SemiNormedSpace α β ] : HasBoundedSmul α β
  where
    dist_smul_pair' x y₁ y₂ := by simpa [ dist_eq_norm , smul_sub ] using SemiNormedSpace.norm_smul_le x ( y₁ - y₂ )
      dist_pair_smul' x₁ x₂ y := by simpa [ dist_eq_norm , sub_smul ] using SemiNormedSpace.norm_smul_le ( x₁ - x₂ ) y

-- failed to format: format: uncaught backtrack exception
instance NormedField.toNormedSpace : NormedSpace α α where norm_smul_le a b := le_of_eqₓ ( NormedField.norm_mul a b )

theorem norm_smul [SemiNormedSpace α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥*∥x∥ := by
  by_cases' h : s = 0
  ·
    simp [h]
  ·
    refine' le_antisymmₓ (SemiNormedSpace.norm_smul_le s x) _
    calc (∥s∥*∥x∥) = ∥s∥*∥s⁻¹ • s • x∥ := by
      rw [inv_smul_smul₀ h]_ ≤ ∥s∥*∥s⁻¹∥*∥s • x∥ :=
      mul_le_mul_of_nonneg_left (SemiNormedSpace.norm_smul_le _ _) (norm_nonneg _)_ = ∥s • x∥ := by
      rw [NormedField.norm_inv, ← mul_assocₓ, mul_inv_cancel (mt norm_eq_zero.1 h), one_mulₓ]

@[simp]
theorem abs_norm_eq_norm (z : β) : |∥z∥| = ∥z∥ :=
  (abs_eq (norm_nonneg z)).mpr (Or.inl rfl)

theorem dist_smul [SemiNormedSpace α β] (s : α) (x y : β) : dist (s • x) (s • y) = ∥s∥*dist x y := by
  simp only [dist_eq_norm, (norm_smul _ _).symm, smul_sub]

theorem nnnorm_smul [SemiNormedSpace α β] (s : α) (x : β) : ∥s • x∥₊ = ∥s∥₊*∥x∥₊ :=
  Nnreal.eq $ norm_smul s x

theorem nndist_smul [SemiNormedSpace α β] (s : α) (x y : β) : nndist (s • x) (s • y) = ∥s∥₊*nndist x y :=
  Nnreal.eq $ dist_smul s x y

theorem norm_smul_of_nonneg [SemiNormedSpace ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) : ∥t • x∥ = t*∥x∥ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

variable {E : Type _} [SemiNormedGroup E] [SemiNormedSpace α E]

variable {F : Type _} [SemiNormedGroup F] [SemiNormedSpace α F]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `eventually_nhds_norm_smul_sub_lt [])
  (Command.declSig
   [(Term.explicitBinder "(" [`c] [":" `α] [] ")")
    (Term.explicitBinder "(" [`x] [":" `E] [] ")")
    (Term.implicitBinder "{" [`ε] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
    (Term.explicitBinder "(" [`h] [":" («term_<_» (numLit "0") "<" `ε)] [] ")")]
   (Term.typeSpec
    ":"
    (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
     "∀ᶠ"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
     " in "
     (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
     ", "
     («term_<_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x)) "∥")
      "<"
      `ε))))
  (Command.declValSimple
   ":="
   (Term.have
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
            [(Term.simpleBinder [`y] [])]
            "=>"
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x))
             "∥")))
          (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
          (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])]))]
      ":="
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app
          (Term.proj `continuous_const "." `smul)
          [(Term.app (Term.proj `continuous_id "." `sub) [`continuous_const])])
         "."
         `norm)
        "."
        `tendsto')
       [(Term.hole "_")
        (Term.hole "_")
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))])))
    []
    (Term.app `this.eventually [(Term.app `gt_mem_nhds [`h])]))
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
  (Term.have
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
           [(Term.simpleBinder [`y] [])]
           "=>"
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x))
            "∥")))
         (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
         (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])]))]
     ":="
     (Term.app
      (Term.proj
       (Term.proj
        (Term.app
         (Term.proj `continuous_const "." `smul)
         [(Term.app (Term.proj `continuous_id "." `sub) [`continuous_const])])
        "."
        `norm)
       "."
       `tendsto')
      [(Term.hole "_")
       (Term.hole "_")
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))])))
   []
   (Term.app `this.eventually [(Term.app `gt_mem_nhds [`h])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `this.eventually [(Term.app `gt_mem_nhds [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `gt_mem_nhds [`h])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `gt_mem_nhds
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `gt_mem_nhds [`h]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this.eventually
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   (Term.proj
    (Term.proj
     (Term.app
      (Term.proj `continuous_const "." `smul)
      [(Term.app (Term.proj `continuous_id "." `sub) [`continuous_const])])
     "."
     `norm)
    "."
    `tendsto')
   [(Term.hole "_")
    (Term.hole "_")
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))) []]
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
  (Term.proj
   (Term.proj
    (Term.app
     (Term.proj `continuous_const "." `smul)
     [(Term.app (Term.proj `continuous_id "." `sub) [`continuous_const])])
    "."
    `norm)
   "."
   `tendsto')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj
   (Term.app
    (Term.proj `continuous_const "." `smul)
    [(Term.app (Term.proj `continuous_id "." `sub) [`continuous_const])])
   "."
   `norm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj `continuous_const "." `smul)
   [(Term.app (Term.proj `continuous_id "." `sub) [`continuous_const])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `continuous_id "." `sub) [`continuous_const])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `continuous_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `continuous_id "." `sub)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `continuous_id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `continuous_id "." `sub) [`continuous_const]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `continuous_const "." `smul)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `continuous_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj `continuous_const "." `smul)
   [(Term.paren "(" [(Term.app (Term.proj `continuous_id "." `sub) [`continuous_const]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `tendsto
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y] [])]
      "=>"
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x)) "∥")))
    (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
    (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
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
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app (Topology.Basic.term𝓝 "𝓝") [`x]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y] [])]
    "=>"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x)) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x)) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `y "-" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `y "-" `x) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y] [])]
    "=>"
    (Analysis.Normed.Group.Basic.«term∥_∥»
     "∥"
     (Algebra.Group.Defs.«term_•_» `c " • " (Term.paren "(" [(«term_-_» `y "-" `x) []] ")"))
     "∥")))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tendsto
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
   " in "
   (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
   ", "
   («term_<_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x)) "∥")
    "<"
    `ε))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x)) "∥")
   "<"
   `ε)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x)) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» `c " • " («term_-_» `y "-" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `y "-" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `y "-" `x) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
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
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  eventually_nhds_norm_smul_sub_lt
  ( c : α ) ( x : E ) { ε : ℝ } ( h : 0 < ε ) : ∀ᶠ y in 𝓝 x , ∥ c • y - x ∥ < ε
  :=
    have
      : tendsto fun y => ∥ c • y - x ∥ 𝓝 x 𝓝 0
        :=
        continuous_const . smul continuous_id . sub continuous_const . norm . tendsto' _ _ by simp
      this.eventually gt_mem_nhds h

theorem closure_ball [SemiNormedSpace ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : Closure (ball x r) = closed_ball x r := by
  refine' Set.Subset.antisymm closure_ball_subset_closed_ball fun y hy => _
  have : ContinuousWithinAt (fun c : ℝ => (c • (y - x))+x) (Set.Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).ContinuousWithinAt
  convert this.mem_closure _ _
  ·
    rw [one_smul, sub_add_cancel]
  ·
    simp [closure_Ico (@zero_lt_one ℝ _ _), zero_le_one]
  ·
    rintro c ⟨hc0, hc1⟩
    rw [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0,
      mul_commₓ, ← mul_oneₓ r]
    rw [mem_closed_ball, dist_eq_norm] at hy
    apply mul_lt_mul' <;> assumption

theorem frontier_ball [SemiNormedSpace ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : Frontier (ball x r) = sphere x r := by
  rw [Frontier, closure_ball x hr, is_open_ball.interior_eq]
  ext x
  exact (@eq_iff_le_not_lt ℝ _ _ _).symm

theorem interior_closed_ball [SemiNormedSpace ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
    Interior (closed_ball x r) = ball x r := by
  refine' Set.Subset.antisymm _ ball_subset_interior_closed_ball
  intro y hy
  rcases le_iff_lt_or_eqₓ.1 (mem_closed_ball.1 $ interior_subset hy) with (hr | rfl)
  ·
    exact hr
  set f : ℝ → E := fun c : ℝ => (c • (y - x))+x
  suffices f ⁻¹' closed_ball x (dist y x) ⊆ Set.Icc (-1) 1by
    have hfc : Continuous f := (continuous_id.smul continuous_const).add continuous_const
    have hf1 : (1 : ℝ) ∈ f ⁻¹' Interior (closed_ball x $ dist y x) := by
      simpa [f]
    have h1 : (1 : ℝ) ∈ Interior (Set.Icc (-1 : ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1)
    contrapose h1
    simp
  intro c hc
  rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← mul_le_mul_right hr]
  simpa [f, dist_eq_norm, norm_smul] using hc

theorem frontier_closed_ball [SemiNormedSpace ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
    Frontier (closed_ball x r) = sphere x r := by
  rw [Frontier, closure_closed_ball, interior_closed_ball x hr, closed_ball_diff_ball]

theorem smul_ball {c : α} (hc : c ≠ 0) (x : E) (r : ℝ) : c • ball x r = ball (c • x) (∥c∥*r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp [← div_eq_inv_mul, div_lt_iff (norm_pos_iff.2 hc), mul_commₓ _ r, dist_smul]

theorem smul_sphere' {c : α} (hc : c ≠ 0) (x : E) (r : ℝ) : c • sphere x r = sphere (c • x) (∥c∥*r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp only [mem_sphere, dist_smul, NormedField.norm_inv, ← div_eq_inv_mul, div_eq_iff (norm_pos_iff.2 hc).ne',
    mul_commₓ r]

/--  In a nontrivial real normed space, a sphere is nonempty if and only if its radius is
nonnegative. -/
@[simp]
theorem NormedSpace.sphere_nonempty {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [Nontrivial E] {x : E} {r : ℝ} :
    (sphere x r).Nonempty ↔ 0 ≤ r := by
  refine' ⟨fun h => nonempty_closed_ball.1 (h.mono sphere_subset_closed_ball), fun hr => _⟩
  rcases exists_ne x with ⟨y, hy⟩
  have : ∥y - x∥ ≠ 0 := by
    simpa [sub_eq_zero]
  use (r • ∥y - x∥⁻¹ • (y - x))+x
  simp [norm_smul, this, Real.norm_of_nonneg hr]

theorem smul_sphere {E : Type _} [NormedGroup E] [NormedSpace α E] [NormedSpace ℝ E] [Nontrivial E] (c : α) (x : E)
    {r : ℝ} (hr : 0 ≤ r) : c • sphere x r = sphere (c • x) (∥c∥*r) := by
  rcases eq_or_ne c 0 with (rfl | hc)
  ·
    simp [zero_smul_set, Set.singleton_zero, hr]
  ·
    exact smul_sphere' hc x r

theorem smul_closed_ball' {c : α} (hc : c ≠ 0) (x : E) (r : ℝ) : c • closed_ball x r = closed_ball (c • x) (∥c∥*r) := by
  simp only [← ball_union_sphere, Set.smul_set_union, smul_ball hc, smul_sphere' hc]

theorem smul_closed_ball {E : Type _} [NormedGroup E] [NormedSpace α E] (c : α) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    c • closed_ball x r = closed_ball (c • x) (∥c∥*r) := by
  rcases eq_or_ne c 0 with (rfl | hc)
  ·
    simp [hr, zero_smul_set, Set.singleton_zero, ← nonempty_closed_ball]
  ·
    exact smul_closed_ball' hc x r

/--  A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ∥x∥)⁻¹ • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`homeomorph_unit_ball_apply_coe` and `homeomorph_unit_ball_symm_apply` as `@[simp]`. -/
@[simps (config := { attrs := [] })]
def homeomorphUnitBall {E : Type _} [SemiNormedGroup E] [SemiNormedSpace ℝ E] : E ≃ₜ ball (0 : E) 1 :=
  { toFun := fun x =>
      ⟨(1+∥x∥)⁻¹ • x, by
        have : ∥x∥ < |1+∥x∥| := (lt_one_add _).trans_le (le_abs_self _)
        rwa [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← div_eq_inv_mul,
          div_lt_one ((norm_nonneg x).trans_lt this)]⟩,
    invFun := fun x => (1 - ∥(x : E)∥)⁻¹ • (x : E),
    left_inv := fun x => by
      have : 0 < 1+∥x∥ := (norm_nonneg x).trans_lt (lt_one_add _)
      field_simp [this.ne', abs_of_pos this, norm_smul, smul_smul, Real.norm_eq_abs, abs_div],
    right_inv := fun x =>
      Subtype.ext
        (by
          have : 0 < 1 - ∥(x : E)∥ := sub_pos.2 (mem_ball_zero_iff.1 x.2)
          field_simp [norm_smul, smul_smul, Real.norm_eq_abs, abs_div, abs_of_pos this, this.ne']),
    continuous_to_fun :=
      continuous_subtype_mk _ $
        ((continuous_const.add continuous_norm).inv₀ fun x => ((norm_nonneg x).trans_lt (lt_one_add _)).ne').smul
          continuous_id,
    continuous_inv_fun :=
      Continuous.smul
        ((continuous_const.sub continuous_subtype_coe.norm).inv₀ $ fun x => (sub_pos.2 $ mem_ball_zero_iff.1 x.2).ne')
        continuous_subtype_coe }

variable (α)

theorem ne_neg_of_mem_sphere [CharZero α] {r : ℝ} (hr : 0 < r) (x : sphere (0 : E) r) : x ≠ -x := fun h =>
  nonzero_of_mem_sphere hr x
    (eq_zero_of_eq_neg α
      (by
        conv_lhs => rw [h]
        simp ))

theorem ne_neg_of_mem_unit_sphere [CharZero α] (x : sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere α
    (by
      norm_num)
    x

variable {α}

open NormedField

/--  The product of two seminormed spaces is a seminormed space, with the sup norm. -/
instance Prod.semiNormedSpace : SemiNormedSpace α (E × F) :=
  { Prod.normedGroup, Prod.module with
    norm_smul_le := fun s x =>
      le_of_eqₓ $ by
        simp [Prod.semi_norm_def, norm_smul, mul_max_of_nonneg] }

-- failed to format: format: uncaught backtrack exception
/-- The product of finitely many seminormed spaces is a seminormed space, with the sup norm. -/
  instance
    Pi.semiNormedSpace
    { E : ι → Type _ } [ Fintype ι ] [ ∀ i , SemiNormedGroup ( E i ) ] [ ∀ i , SemiNormedSpace α ( E i ) ]
      : SemiNormedSpace α ( ∀ i , E i )
    where
      norm_smul_le
        a f
        :=
        le_of_eqₓ
          $
          show
            ( ↑ Finset.sup Finset.univ fun b : ι => ∥ a • f b ∥₊ : ℝ )
              =
              ∥ a ∥₊ * ↑ Finset.sup Finset.univ fun b : ι => ∥ f b ∥₊
            by simp only [ ( Nnreal.coe_mul _ _ ) . symm , Nnreal.mul_finset_sup , nnnorm_smul ]

-- failed to format: format: uncaught backtrack exception
/-- A subspace of a seminormed space is also a normed space, with the restriction of the norm. -/
  instance
    Submodule.semiNormedSpace
    { 𝕜 R : Type _ }
        [ HasScalar 𝕜 R ]
        [ NormedField 𝕜 ]
        [ Ringₓ R ]
        { E : Type _ }
        [ SemiNormedGroup E ]
        [ SemiNormedSpace 𝕜 E ]
        [ Module R E ]
        [ IsScalarTower 𝕜 R E ]
        ( s : Submodule R E )
      : SemiNormedSpace 𝕜 s
    where norm_smul_le c x := le_of_eqₓ $ norm_smul c ( x : E )

/--  If there is a scalar `c` with `∥c∥>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `∥c∥`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
theorem rescale_to_shell_semi_normed {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : ∥x∥ ≠ 0) :
    ∃ d : α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ ε / ∥c∥ ≤ ∥d • x∥ ∧ ∥d∥⁻¹ ≤ (ε⁻¹*∥c∥)*∥x∥ := by
  have xεpos : 0 < ∥x∥ / ε := div_pos ((Ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ∥c∥ := lt_transₓ (zero_lt_one : (0 : ℝ) < 1) hc
  have cnpos : 0 < ∥c ^ n+1∥ := by
    rw [norm_zpow]
    exact lt_transₓ xεpos hn.2
  refine' ⟨(c ^ n+1)⁻¹, _, _, _, _⟩
  show (c ^ n+1)⁻¹ ≠ 0
  ·
    rwa [Ne.def, inv_eq_zero, ← Ne.def, ← norm_pos_iff]
  show ∥(c ^ n+1)⁻¹ • x∥ < ε
  ·
    rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_lt_iff cnpos, mul_commₓ, norm_zpow]
    exact (div_lt_iff εpos).1 hn.2
  show ε / ∥c∥ ≤ ∥(c ^ n+1)⁻¹ • x∥
  ·
    rw [div_le_iff cpos, norm_smul, norm_inv, norm_zpow, zpow_add₀ (ne_of_gtₓ cpos), zpow_one, mul_inv_rev₀, mul_commₓ,
      ← mul_assocₓ, ← mul_assocₓ, mul_inv_cancel (ne_of_gtₓ cpos), one_mulₓ, ← div_eq_inv_mul,
      le_div_iff (zpow_pos_of_pos cpos _), mul_commₓ]
    exact (le_div_iff εpos).1 hn.1
  show ∥(c ^ n+1)⁻¹∥⁻¹ ≤ (ε⁻¹*∥c∥)*∥x∥
  ·
    have : ((ε⁻¹*∥c∥)*∥x∥) = (ε⁻¹*∥x∥)*∥c∥ := by
      ring
    rw [norm_inv, inv_inv₀, norm_zpow, zpow_add₀ (ne_of_gtₓ cpos), zpow_one, this, ← div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _)

end SemiNormedSpace

section NormedSpace

variable [NormedField α]

variable {E : Type _} [NormedGroup E] [NormedSpace α E]

variable {F : Type _} [NormedGroup F] [NormedSpace α F]

open NormedField

theorem interior_closed_ball' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    Interior (closed_ball x r) = ball x r := by
  rcases lt_trichotomyₓ r 0 with (hr | rfl | hr)
  ·
    simp [closed_ball_eq_empty.2 hr, ball_eq_empty.2 hr.le]
  ·
    rw [closed_ball_zero, ball_zero, interior_singleton]
  ·
    exact interior_closed_ball x hr

theorem frontier_closed_ball' [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) :
    Frontier (closed_ball x r) = sphere x r := by
  rw [Frontier, closure_closed_ball, interior_closed_ball' x r, closed_ball_diff_ball]

variable {α}

/--  If there is a scalar `c` with `∥c∥>1`, then any element can be moved by scalar multiplication to
any shell of width `∥c∥`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
theorem rescale_to_shell {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
    ∃ d : α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ ε / ∥c∥ ≤ ∥d • x∥ ∧ ∥d∥⁻¹ ≤ (ε⁻¹*∥c∥)*∥x∥ :=
  rescale_to_shell_semi_normed hc εpos (ne_of_ltₓ (norm_pos_iff.2 hx)).symm

/--  The product of two normed spaces is a normed space, with the sup norm. -/
instance : NormedSpace α (E × F) :=
  { Prod.semiNormedSpace with }

/--  The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance Pi.normedSpace {E : ι → Type _} [Fintype ι] [∀ i, NormedGroup (E i)] [∀ i, NormedSpace α (E i)] :
    NormedSpace α (∀ i, E i) :=
  { Pi.semiNormedSpace with }

section

attribute [local instance] Matrix.normedGroup

/--  Normed space instance (using sup norm of sup norm) for matrices over a normed field.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
def Matrix.normedSpace {α : Type _} [NormedField α] {n m : Type _} [Fintype n] [Fintype m] :
    NormedSpace α (Matrix n m α) :=
  Pi.normedSpace

end

/--  A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance Submodule.normedSpace {𝕜 R : Type _} [HasScalar 𝕜 R] [NormedField 𝕜] [Ringₓ R] {E : Type _} [NormedGroup E]
    [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E] (s : Submodule R E) : NormedSpace 𝕜 s :=
  { Submodule.semiNormedSpace s with }

end NormedSpace

section NormedAlgebra

/--  A seminormed algebra `𝕜'` over `𝕜` is an algebra endowed with a seminorm for which the
embedding of `𝕜` in `𝕜'` is an isometry. -/
class SemiNormedAlgebra (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [SemiNormedRing 𝕜'] extends Algebra 𝕜 𝕜' where
  norm_algebra_map_eq : ∀ x : 𝕜, ∥algebraMap 𝕜 𝕜' x∥ = ∥x∥

/--  A normed algebra `𝕜'` over `𝕜` is an algebra endowed with a norm for which the embedding of
`𝕜` in `𝕜'` is an isometry. -/
class NormedAlgebra (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [NormedRing 𝕜'] extends Algebra 𝕜 𝕜' where
  norm_algebra_map_eq : ∀ x : 𝕜, ∥algebraMap 𝕜 𝕜' x∥ = ∥x∥

/--  A normed algebra is a seminormed algebra. -/
instance (priority := 100) NormedAlgebra.toSemiNormedAlgebra (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [NormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] : SemiNormedAlgebra 𝕜 𝕜' where
  norm_algebra_map_eq := NormedAlgebra.norm_algebra_map_eq

@[simp]
theorem norm_algebra_map_eq {𝕜 : Type _} (𝕜' : Type _) [NormedField 𝕜] [SemiNormedRing 𝕜'] [h : SemiNormedAlgebra 𝕜 𝕜']
    (x : 𝕜) : ∥algebraMap 𝕜 𝕜' x∥ = ∥x∥ :=
  SemiNormedAlgebra.norm_algebra_map_eq _

/--  In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
theorem algebra_map_isometry (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [SemiNormedRing 𝕜'] [SemiNormedAlgebra 𝕜 𝕜'] :
    Isometry (algebraMap 𝕜 𝕜') := by
  refine' isometry_emetric_iff_metric.2 fun x y => _
  rw [dist_eq_norm, dist_eq_norm, ← RingHom.map_sub, norm_algebra_map_eq]

variable (𝕜 : Type _) [NormedField 𝕜]

variable (𝕜' : Type _) [SemiNormedRing 𝕜']

instance (priority := 100) SemiNormedAlgebra.toSemiNormedSpace [h : SemiNormedAlgebra 𝕜 𝕜'] : SemiNormedSpace 𝕜 𝕜' :=
  { h with
    norm_smul_le := fun s x =>
      calc ∥s • x∥ = ∥(algebraMap 𝕜 𝕜') s*x∥ := by
        rw [h.smul_def']
        rfl
        _ ≤ ∥algebraMap 𝕜 𝕜' s∥*∥x∥ := SemiNormedRing.norm_mul _ _
        _ = ∥s∥*∥x∥ := by
        rw [norm_algebra_map_eq]
         }

/--  While this may appear identical to `semi_normed_algebra.to_semi_normed_space`, it contains an
implicit argument involving `normed_ring.to_semi_normed_ring` that typeclass inference has trouble
inferring.

Specifically, the following instance cannot be found without this
`semi_normed_algebra.to_semi_normed_space'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_ring (E i)] [Π i, normed_algebra 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

See `semi_normed_space.to_module'` for a similar situation. -/
instance (priority := 100) SemiNormedAlgebra.toSemiNormedSpace' (𝕜 : Type _) [NormedField 𝕜] (𝕜' : Type _)
    [NormedRing 𝕜'] [SemiNormedAlgebra 𝕜 𝕜'] : SemiNormedSpace 𝕜 𝕜' := by
  infer_instance

instance (priority := 100) NormedAlgebra.toNormedSpace (𝕜 : Type _) [NormedField 𝕜] (𝕜' : Type _) [NormedRing 𝕜']
    [h : NormedAlgebra 𝕜 𝕜'] : NormedSpace 𝕜 𝕜' :=
  { h with norm_smul_le := SemiNormedSpace.norm_smul_le }

instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { Algebra.id 𝕜 with
    norm_algebra_map_eq := by
      simp }

variable (𝕜') [SemiNormedAlgebra 𝕜 𝕜']

include 𝕜

theorem NormedAlgebra.norm_one : ∥(1 : 𝕜')∥ = 1 := by
  simpa using norm_algebra_map_eq 𝕜' (1 : 𝕜)

theorem NormedAlgebra.norm_one_class : NormOneClass 𝕜' :=
  ⟨NormedAlgebra.norm_one 𝕜 𝕜'⟩

theorem NormedAlgebra.zero_ne_one : (0 : 𝕜') ≠ 1 := by
  refine' (ne_zero_of_norm_pos _).symm
  rw [NormedAlgebra.norm_one 𝕜 𝕜']
  norm_num

theorem NormedAlgebra.nontrivial : Nontrivial 𝕜' :=
  ⟨⟨0, 1, NormedAlgebra.zero_ne_one 𝕜 𝕜'⟩⟩

end NormedAlgebra

section RestrictScalars

variable (𝕜 : Type _) (𝕜' : Type _) [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] (E : Type _) [NormedGroup E]
  [NormedSpace 𝕜' E] (F : Type _) [SemiNormedGroup F] [SemiNormedSpace 𝕜' F]

/--  Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-seminormed space structure induced by a `𝕜'`-seminormed space structure when `𝕜'` is a
seminormed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `module.restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def SemiNormedSpace.restrictScalars : SemiNormedSpace 𝕜 F :=
  { RestrictScalars.module 𝕜 𝕜' F with
    norm_smul_le := fun c x =>
      le_of_eqₓ $ by
        change ∥algebraMap 𝕜 𝕜' c • x∥ = ∥c∥*∥x∥
        simp [norm_smul] }

/--  Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-normed space structure induced by a `𝕜'`-normed space structure when `𝕜'` is a
normed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  { RestrictScalars.module 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
      le_of_eqₓ $ by
        change ∥algebraMap 𝕜 𝕜' c • x∥ = ∥c∥*∥x∥
        simp [norm_smul] }

instance {𝕜 : Type _} {𝕜' : Type _} {F : Type _} [I : SemiNormedGroup F] : SemiNormedGroup (RestrictScalars 𝕜 𝕜' F) :=
  I

instance {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [I : NormedGroup E] : NormedGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

instance Module.RestrictScalars.semiNormedSpaceOrig {𝕜 : Type _} {𝕜' : Type _} {F : Type _} [NormedField 𝕜']
    [SemiNormedGroup F] [I : SemiNormedSpace 𝕜' F] : SemiNormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' F) :=
  I

instance Module.RestrictScalars.normedSpaceOrig {𝕜 : Type _} {𝕜' : Type _} {E : Type _} [NormedField 𝕜'] [NormedGroup E]
    [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I

instance : SemiNormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' F) :=
  (SemiNormedSpace.restrictScalars 𝕜 𝕜' F : SemiNormedSpace 𝕜 F)

instance : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  (NormedSpace.restrictScalars 𝕜 𝕜' E : NormedSpace 𝕜 E)

end RestrictScalars

section CauchyProduct

/-! ## Multiplying two infinite sums in a normed ring

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `topology/algebra/infinite_sum` (e.g `tsum_mul_tsum`),
but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `β` and `γ`, and then we specialize to
`β = γ = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).

### Arbitrary index types
-/


variable {ι' : Type _} [NormedRing α]

open Finset

open_locale Classical

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Summable.mul_of_nonneg [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" (Data.Real.Basic.termℝ "ℝ"))] "}")
    (Term.implicitBinder "{" [`g] [":" (Term.arrow `ι' "→" (Data.Real.Basic.termℝ "ℝ"))] "}")
    (Term.explicitBinder "(" [`hf] [":" (Term.app `Summable [`f])] [] ")")
    (Term.explicitBinder "(" [`hg] [":" (Term.app `Summable [`g])] [] ")")
    (Term.explicitBinder "(" [`hf'] [":" («term_≤_» (numLit "0") "≤" `f)] [] ")")
    (Term.explicitBinder "(" [`hg'] [":" («term_≤_» (numLit "0") "≤" `g)] [] ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `Summable
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x] [(Term.typeSpec ":" («term_×_» `ι "×" `ι'))])]
        "=>"
        (Finset.Data.Finset.Fold.«term_*_»
         (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
         "*"
         (Term.app `g [(Term.proj `x "." (fieldIdx "2"))]))))])))
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`s "," `hf] "⟩") [] [] ":=" `hf))
    []
    (Term.let
     "let"
     (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`t "," `hg] "⟩") [] [] ":=" `hg))
     []
     (Term.suffices
      "suffices"
      (Term.sufficesDecl
       [`this ":"]
       (Term.forall
        "∀"
        [(Term.simpleBinder [`u] [(Term.typeSpec ":" (Term.app `Finset [(«term_×_» `ι "×" `ι')]))])]
        ","
        («term_≤_»
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          `u
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
           "*"
           (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
         "≤"
         (Finset.Data.Finset.Fold.«term_*_» `s "*" `t)))
       (Term.fromTerm
        "from"
        (Term.app
         `summable_of_sum_le
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
          `this])))
      []
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`u] [])]
        "=>"
        (calc
         "calc"
         [(calcStep
           («term_≤_»
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             `u
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
              "*"
              (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
            "≤"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (Term.app (Term.proj (Term.app `u.image [`Prod.fst]) "." `product) [(Term.app `u.image [`Prod.snd])])
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
              "*"
              (Term.app `g [(Term.proj `x "." (fieldIdx "2"))]))))
           ":="
           (Term.app
            `sum_mono_set_of_nonneg
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x] [])]
               "=>"
               (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
             `subset_product]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (Term.app `u.image [`Prod.fst])
             ", "
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
              " in "
              (Term.app `u.image [`Prod.snd])
              ", "
              (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" (Term.app `g [`y])))))
           ":="
           `sum_product)
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (Term.app `u.image [`Prod.fst])
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f [`x])
              "*"
              (Algebra.BigOperators.Basic.«term∑_in_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
               " in "
               (Term.app `u.image [`Prod.snd])
               ", "
               (Term.app `g [`y])))))
           ":="
           (Term.app
            `sum_congr
            [`rfl
             (Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Term.proj `mul_sum "." `symm)))]))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (Term.app `u.image [`Prod.fst])
             ", "
             (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" `t)))
           ":="
           (Term.app
            `sum_le_sum
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x (Term.hole "_")] [])]
               "=>"
               (Term.app
                `mul_le_mul_of_nonneg_left
                [(Term.app
                  `sum_le_has_sum
                  [(Term.hole "_")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                     "=>"
                     (Term.app `hg' [(Term.hole "_")])))
                   `hg])
                 (Term.app `hf' [(Term.hole "_")])])))]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
              " in "
              (Term.app `u.image [`Prod.fst])
              ", "
              (Term.app `f [`x]))
             "*"
             `t))
           ":="
           (Term.proj `sum_mul "." `symm))
          (calcStep
           («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `s "*" `t))
           ":="
           (Term.app
            `mul_le_mul_of_nonneg_right
            [(Term.app
              `sum_le_has_sum
              [(Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                 "=>"
                 (Term.app `hf' [(Term.hole "_")])))
               `hf])
             («term_$__»
              `hg.nonneg
              "$"
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [(Term.hole "_")] [])]
                "=>"
                (Term.app `hg' [(Term.hole "_")]))))]))]))))))
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
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`s "," `hf] "⟩") [] [] ":=" `hf))
   []
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`t "," `hg] "⟩") [] [] ":=" `hg))
    []
    (Term.suffices
     "suffices"
     (Term.sufficesDecl
      [`this ":"]
      (Term.forall
       "∀"
       [(Term.simpleBinder [`u] [(Term.typeSpec ":" (Term.app `Finset [(«term_×_» `ι "×" `ι')]))])]
       ","
       («term_≤_»
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         " in "
         `u
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
          "*"
          (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
        "≤"
        (Finset.Data.Finset.Fold.«term_*_» `s "*" `t)))
      (Term.fromTerm
       "from"
       (Term.app
        `summable_of_sum_le
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
         `this])))
     []
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`u] [])]
       "=>"
       (calc
        "calc"
        [(calcStep
          («term_≤_»
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            " in "
            `u
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
             "*"
             (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            " in "
            (Term.app (Term.proj (Term.app `u.image [`Prod.fst]) "." `product) [(Term.app `u.image [`Prod.snd])])
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
             "*"
             (Term.app `g [(Term.proj `x "." (fieldIdx "2"))]))))
          ":="
          (Term.app
           `sum_mono_set_of_nonneg
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x] [])]
              "=>"
              (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
            `subset_product]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            " in "
            (Term.app `u.image [`Prod.fst])
            ", "
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
             " in "
             (Term.app `u.image [`Prod.snd])
             ", "
             (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" (Term.app `g [`y])))))
          ":="
          `sum_product)
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            " in "
            (Term.app `u.image [`Prod.fst])
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app `f [`x])
             "*"
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
              " in "
              (Term.app `u.image [`Prod.snd])
              ", "
              (Term.app `g [`y])))))
          ":="
          (Term.app
           `sum_congr
           [`rfl
            (Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Term.proj `mul_sum "." `symm)))]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            " in "
            (Term.app `u.image [`Prod.fst])
            ", "
            (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" `t)))
          ":="
          (Term.app
           `sum_le_sum
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x (Term.hole "_")] [])]
              "=>"
              (Term.app
               `mul_le_mul_of_nonneg_left
               [(Term.app
                 `sum_le_has_sum
                 [(Term.hole "_")
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                    "=>"
                    (Term.app `hg' [(Term.hole "_")])))
                  `hg])
                (Term.app `hf' [(Term.hole "_")])])))]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             " in "
             (Term.app `u.image [`Prod.fst])
             ", "
             (Term.app `f [`x]))
            "*"
            `t))
          ":="
          (Term.proj `sum_mul "." `symm))
         (calcStep
          («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `s "*" `t))
          ":="
          (Term.app
           `mul_le_mul_of_nonneg_right
           [(Term.app
             `sum_le_has_sum
             [(Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                "=>"
                (Term.app `hf' [(Term.hole "_")])))
              `hf])
            («term_$__»
             `hg.nonneg
             "$"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [(Term.hole "_")] [])]
               "=>"
               (Term.app `hg' [(Term.hole "_")]))))]))]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`t "," `hg] "⟩") [] [] ":=" `hg))
   []
   (Term.suffices
    "suffices"
    (Term.sufficesDecl
     [`this ":"]
     (Term.forall
      "∀"
      [(Term.simpleBinder [`u] [(Term.typeSpec ":" (Term.app `Finset [(«term_×_» `ι "×" `ι')]))])]
      ","
      («term_≤_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        " in "
        `u
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
         "*"
         (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
       "≤"
       (Finset.Data.Finset.Fold.«term_*_» `s "*" `t)))
     (Term.fromTerm
      "from"
      (Term.app
       `summable_of_sum_le
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
        `this])))
    []
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`u] [])]
      "=>"
      (calc
       "calc"
       [(calcStep
         («term_≤_»
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           `u
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
            "*"
            (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
          "≤"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           (Term.app (Term.proj (Term.app `u.image [`Prod.fst]) "." `product) [(Term.app `u.image [`Prod.snd])])
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
            "*"
            (Term.app `g [(Term.proj `x "." (fieldIdx "2"))]))))
         ":="
         (Term.app
          `sum_mono_set_of_nonneg
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [])]
             "=>"
             (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
           `subset_product]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           (Term.app `u.image [`Prod.fst])
           ", "
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
            " in "
            (Term.app `u.image [`Prod.snd])
            ", "
            (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" (Term.app `g [`y])))))
         ":="
         `sum_product)
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           (Term.app `u.image [`Prod.fst])
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.app `f [`x])
            "*"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
             " in "
             (Term.app `u.image [`Prod.snd])
             ", "
             (Term.app `g [`y])))))
         ":="
         (Term.app
          `sum_congr
          [`rfl
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Term.proj `mul_sum "." `symm)))]))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           (Term.app `u.image [`Prod.fst])
           ", "
           (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" `t)))
         ":="
         (Term.app
          `sum_le_sum
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x (Term.hole "_")] [])]
             "=>"
             (Term.app
              `mul_le_mul_of_nonneg_left
              [(Term.app
                `sum_le_has_sum
                [(Term.hole "_")
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                   "=>"
                   (Term.app `hg' [(Term.hole "_")])))
                 `hg])
               (Term.app `hf' [(Term.hole "_")])])))]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Finset.Data.Finset.Fold.«term_*_»
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
            " in "
            (Term.app `u.image [`Prod.fst])
            ", "
            (Term.app `f [`x]))
           "*"
           `t))
         ":="
         (Term.proj `sum_mul "." `symm))
        (calcStep
         («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `s "*" `t))
         ":="
         (Term.app
          `mul_le_mul_of_nonneg_right
          [(Term.app
            `sum_le_has_sum
            [(Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
               "=>"
               (Term.app `hf' [(Term.hole "_")])))
             `hf])
           («term_$__»
            `hg.nonneg
            "$"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [(Term.hole "_")] [])]
              "=>"
              (Term.app `hg' [(Term.hole "_")]))))]))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.suffices
   "suffices"
   (Term.sufficesDecl
    [`this ":"]
    (Term.forall
     "∀"
     [(Term.simpleBinder [`u] [(Term.typeSpec ":" (Term.app `Finset [(«term_×_» `ι "×" `ι')]))])]
     ","
     («term_≤_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       " in "
       `u
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
        "*"
        (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
      "≤"
      (Finset.Data.Finset.Fold.«term_*_» `s "*" `t)))
    (Term.fromTerm
     "from"
     (Term.app
      `summable_of_sum_le
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x] [])]
         "=>"
         (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
       `this])))
   []
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`u] [])]
     "=>"
     (calc
      "calc"
      [(calcStep
        («term_≤_»
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          `u
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
           "*"
           (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
         "≤"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          (Term.app (Term.proj (Term.app `u.image [`Prod.fst]) "." `product) [(Term.app `u.image [`Prod.snd])])
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
           "*"
           (Term.app `g [(Term.proj `x "." (fieldIdx "2"))]))))
        ":="
        (Term.app
         `sum_mono_set_of_nonneg
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
          `subset_product]))
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          (Term.app `u.image [`Prod.fst])
          ", "
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
           " in "
           (Term.app `u.image [`Prod.snd])
           ", "
           (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" (Term.app `g [`y])))))
        ":="
        `sum_product)
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          (Term.app `u.image [`Prod.fst])
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           (Term.app `f [`x])
           "*"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
            " in "
            (Term.app `u.image [`Prod.snd])
            ", "
            (Term.app `g [`y])))))
        ":="
        (Term.app
         `sum_congr
         [`rfl
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Term.proj `mul_sum "." `symm)))]))
       (calcStep
        («term_≤_»
         (Term.hole "_")
         "≤"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          (Term.app `u.image [`Prod.fst])
          ", "
          (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" `t)))
        ":="
        (Term.app
         `sum_le_sum
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x (Term.hole "_")] [])]
            "=>"
            (Term.app
             `mul_le_mul_of_nonneg_left
             [(Term.app
               `sum_le_has_sum
               [(Term.hole "_")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                  "=>"
                  (Term.app `hg' [(Term.hole "_")])))
                `hg])
              (Term.app `hf' [(Term.hole "_")])])))]))
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Finset.Data.Finset.Fold.«term_*_»
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
           " in "
           (Term.app `u.image [`Prod.fst])
           ", "
           (Term.app `f [`x]))
          "*"
          `t))
        ":="
        (Term.proj `sum_mul "." `symm))
       (calcStep
        («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `s "*" `t))
        ":="
        (Term.app
         `mul_le_mul_of_nonneg_right
         [(Term.app
           `sum_le_has_sum
           [(Term.hole "_")
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
              "=>"
              (Term.app `hf' [(Term.hole "_")])))
            `hf])
          («term_$__»
           `hg.nonneg
           "$"
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `hg' [(Term.hole "_")]))))]))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.suffices', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.suffices', expected 'Lean.Parser.Term.suffices.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`u] [])]
    "=>"
    (calc
     "calc"
     [(calcStep
       («term_≤_»
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         " in "
         `u
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
          "*"
          (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
        "≤"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         " in "
         (Term.app (Term.proj (Term.app `u.image [`Prod.fst]) "." `product) [(Term.app `u.image [`Prod.snd])])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
          "*"
          (Term.app `g [(Term.proj `x "." (fieldIdx "2"))]))))
       ":="
       (Term.app
        `sum_mono_set_of_nonneg
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
         `subset_product]))
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         " in "
         (Term.app `u.image [`Prod.fst])
         ", "
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
          " in "
          (Term.app `u.image [`Prod.snd])
          ", "
          (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" (Term.app `g [`y])))))
       ":="
       `sum_product)
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         " in "
         (Term.app `u.image [`Prod.fst])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          (Term.app `f [`x])
          "*"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
           " in "
           (Term.app `u.image [`Prod.snd])
           ", "
           (Term.app `g [`y])))))
       ":="
       (Term.app
        `sum_congr
        [`rfl
         (Term.fun
          "fun"
          (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Term.proj `mul_sum "." `symm)))]))
      (calcStep
       («term_≤_»
        (Term.hole "_")
        "≤"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         " in "
         (Term.app `u.image [`Prod.fst])
         ", "
         (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" `t)))
       ":="
       (Term.app
        `sum_le_sum
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x (Term.hole "_")] [])]
           "=>"
           (Term.app
            `mul_le_mul_of_nonneg_left
            [(Term.app
              `sum_le_has_sum
              [(Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                 "=>"
                 (Term.app `hg' [(Term.hole "_")])))
               `hg])
             (Term.app `hf' [(Term.hole "_")])])))]))
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Finset.Data.Finset.Fold.«term_*_»
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          " in "
          (Term.app `u.image [`Prod.fst])
          ", "
          (Term.app `f [`x]))
         "*"
         `t))
       ":="
       (Term.proj `sum_mul "." `symm))
      (calcStep
       («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `s "*" `t))
       ":="
       (Term.app
        `mul_le_mul_of_nonneg_right
        [(Term.app
          `sum_le_has_sum
          [(Term.hole "_")
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
             "=>"
             (Term.app `hf' [(Term.hole "_")])))
           `hf])
         («term_$__»
          `hg.nonneg
          "$"
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `hg' [(Term.hole "_")]))))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (calc
   "calc"
   [(calcStep
     («term_≤_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       " in "
       `u
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
        "*"
        (Term.app `g [(Term.proj `x "." (fieldIdx "2"))])))
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       " in "
       (Term.app (Term.proj (Term.app `u.image [`Prod.fst]) "." `product) [(Term.app `u.image [`Prod.snd])])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Term.app `f [(Term.proj `x "." (fieldIdx "1"))])
        "*"
        (Term.app `g [(Term.proj `x "." (fieldIdx "2"))]))))
     ":="
     (Term.app
      `sum_mono_set_of_nonneg
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x] [])]
         "=>"
         (Term.app `mul_nonneg [(Term.app `hf' [(Term.hole "_")]) (Term.app `hg' [(Term.hole "_")])])))
       `subset_product]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       " in "
       (Term.app `u.image [`Prod.fst])
       ", "
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
        " in "
        (Term.app `u.image [`Prod.snd])
        ", "
        (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" (Term.app `g [`y])))))
     ":="
     `sum_product)
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       " in "
       (Term.app `u.image [`Prod.fst])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Term.app `f [`x])
        "*"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
         " in "
         (Term.app `u.image [`Prod.snd])
         ", "
         (Term.app `g [`y])))))
     ":="
     (Term.app
      `sum_congr
      [`rfl
       (Term.fun
        "fun"
        (Term.basicFun [(Term.simpleBinder [`x (Term.hole "_")] [])] "=>" (Term.proj `mul_sum "." `symm)))]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       " in "
       (Term.app `u.image [`Prod.fst])
       ", "
       (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" `t)))
     ":="
     (Term.app
      `sum_le_sum
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x (Term.hole "_")] [])]
         "=>"
         (Term.app
          `mul_le_mul_of_nonneg_left
          [(Term.app
            `sum_le_has_sum
            [(Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
               "=>"
               (Term.app `hg' [(Term.hole "_")])))
             `hg])
           (Term.app `hf' [(Term.hole "_")])])))]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        " in "
        (Term.app `u.image [`Prod.fst])
        ", "
        (Term.app `f [`x]))
       "*"
       `t))
     ":="
     (Term.proj `sum_mul "." `symm))
    (calcStep
     («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `s "*" `t))
     ":="
     (Term.app
      `mul_le_mul_of_nonneg_right
      [(Term.app
        `sum_le_has_sum
        [(Term.hole "_")
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
           "=>"
           (Term.app `hf' [(Term.hole "_")])))
         `hf])
       («term_$__»
        `hg.nonneg
        "$"
        (Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `hg' [(Term.hole "_")]))))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mul_le_mul_of_nonneg_right
   [(Term.app
     `sum_le_has_sum
     [(Term.hole "_")
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
        "=>"
        (Term.app `hf' [(Term.hole "_")])))
      `hf])
    («term_$__»
     `hg.nonneg
     "$"
     (Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `hg' [(Term.hole "_")]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `hg.nonneg
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `hg' [(Term.hole "_")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `hg' [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hg' [(Term.hole "_")])
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
  `hg'
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `hg.nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__»
   `hg.nonneg
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `hg' [(Term.hole "_")]))))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `sum_le_has_sum
   [(Term.hole "_")
    (Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" (Term.app `hf' [(Term.hole "_")])))
    `hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" (Term.app `hf' [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf' [(Term.hole "_")])
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
  `hf'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" (Term.app `hf' [(Term.hole "_")])))
  []]
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
  `sum_le_has_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `sum_le_has_sum
   [(Term.hole "_")
    (Term.paren
     "("
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
        "=>"
        (Term.app `hf' [(Term.hole "_")])))
      []]
     ")")
    `hf])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» `s "*" `t))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `s "*" `t)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.proj `sum_mul "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `sum_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     " in "
     (Term.app `u.image [`Prod.fst])
     ", "
     (Term.app `f [`x]))
    "*"
    `t))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
    " in "
    (Term.app `u.image [`Prod.fst])
    ", "
    (Term.app `f [`x]))
   "*"
   `t)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   " in "
   (Term.app `u.image [`Prod.fst])
   ", "
   (Term.app `f [`x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`x])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `u.image [`Prod.fst])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Prod.fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `u.image
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
theorem
  Summable.mul_of_nonneg
  { f : ι → ℝ } { g : ι' → ℝ } ( hf : Summable f ) ( hg : Summable g ) ( hf' : 0 ≤ f ) ( hg' : 0 ≤ g )
    : Summable fun x : ι × ι' => f x . 1 * g x . 2
  :=
    let
      ⟨ s , hf ⟩ := hf
      let
        ⟨ t , hg ⟩ := hg
        suffices
          this :
            ∀ u : Finset ι × ι' , ∑ x in u , f x . 1 * g x . 2 ≤ s * t
            from summable_of_sum_le fun x => mul_nonneg hf' _ hg' _ this
          fun
            u
              =>
              calc
                ∑ x in u , f x . 1 * g x . 2 ≤ ∑ x in u.image Prod.fst . product u.image Prod.snd , f x . 1 * g x . 2
                    :=
                    sum_mono_set_of_nonneg fun x => mul_nonneg hf' _ hg' _ subset_product
                  _ = ∑ x in u.image Prod.fst , ∑ y in u.image Prod.snd , f x * g y := sum_product
                  _ = ∑ x in u.image Prod.fst , f x * ∑ y in u.image Prod.snd , g y
                    :=
                    sum_congr rfl fun x _ => mul_sum . symm
                  _ ≤ ∑ x in u.image Prod.fst , f x * t
                    :=
                    sum_le_sum fun x _ => mul_le_mul_of_nonneg_left sum_le_has_sum _ fun _ _ => hg' _ hg hf' _
                  _ = ∑ x in u.image Prod.fst , f x * t := sum_mul . symm
                  _ ≤ s * t
                    :=
                    mul_le_mul_of_nonneg_right sum_le_has_sum _ fun _ _ => hf' _ hf hg.nonneg $ fun _ => hg' _

theorem Summable.mul_norm {f : ι → α} {g : ι' → α} (hf : Summable fun x => ∥f x∥) (hg : Summable fun x => ∥g x∥) :
    Summable fun x : ι × ι' => ∥f x.1*g x.2∥ :=
  summable_of_nonneg_of_le (fun x => norm_nonneg (f x.1*g x.2)) (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg $ f x) fun x => norm_nonneg $ g x : _)

theorem summable_mul_of_summable_norm [CompleteSpace α] {f : ι → α} {g : ι' → α} (hf : Summable fun x => ∥f x∥)
    (hg : Summable fun x => ∥g x∥) : Summable fun x : ι × ι' => f x.1*g x.2 :=
  summable_of_summable_norm (hf.mul_norm hg)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Product of two infinites sums indexed by arbitrary types.\n    See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `tsum_mul_tsum_of_summable_norm [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `CompleteSpace [`α]) "]")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" `α)] "}")
    (Term.implicitBinder "{" [`g] [":" (Term.arrow `ι' "→" `α)] "}")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")))])]
     []
     ")")
    (Term.explicitBinder
     "("
     [`hg]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`x]) "∥")))])]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       ", "
       (Term.app `f [`x]))
      "*"
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
       ", "
       (Term.app `g [`y])))
     "="
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `z)] [":" («term_×_» `ι "×" `ι')]))
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.app `f [(Term.proj `z "." (fieldIdx "1"))])
       "*"
       (Term.app `g [(Term.proj `z "." (fieldIdx "2"))]))))))
  (Command.declValSimple
   ":="
   (Term.app
    `tsum_mul_tsum
    [(Term.app `summable_of_summable_norm [`hf])
     (Term.app `summable_of_summable_norm [`hg])
     (Term.app `summable_mul_of_summable_norm [`hf `hg])])
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
   `tsum_mul_tsum
   [(Term.app `summable_of_summable_norm [`hf])
    (Term.app `summable_of_summable_norm [`hg])
    (Term.app `summable_mul_of_summable_norm [`hf `hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `summable_mul_of_summable_norm [`hf `hg])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `summable_mul_of_summable_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `summable_mul_of_summable_norm [`hf `hg]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `summable_of_summable_norm [`hg])
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
  `summable_of_summable_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `summable_of_summable_norm [`hg]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `summable_of_summable_norm [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `summable_of_summable_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `summable_of_summable_norm [`hf]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_mul_tsum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     ", "
     (Term.app `f [`x]))
    "*"
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
     ", "
     (Term.app `g [`y])))
   "="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `z)] [":" («term_×_» `ι "×" `ι')]))
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Term.app `f [(Term.proj `z "." (fieldIdx "1"))])
     "*"
     (Term.app `g [(Term.proj `z "." (fieldIdx "2"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `z)] [":" («term_×_» `ι "×" `ι')]))
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app `f [(Term.proj `z "." (fieldIdx "1"))])
    "*"
    (Term.app `g [(Term.proj `z "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app `f [(Term.proj `z "." (fieldIdx "1"))])
   "*"
   (Term.app `g [(Term.proj `z "." (fieldIdx "2"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [(Term.proj `z "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `z "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `f [(Term.proj `z "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `z "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `z
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    Product of two infinites sums indexed by arbitrary types.
        See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/
  theorem
    tsum_mul_tsum_of_summable_norm
    [ CompleteSpace α ]
        { f : ι → α }
        { g : ι' → α }
        ( hf : Summable fun x => ∥ f x ∥ )
        ( hg : Summable fun x => ∥ g x ∥ )
      : ∑' x , f x * ∑' y , g y = ∑' z : ι × ι' , f z . 1 * g z . 2
    := tsum_mul_tsum summable_of_summable_norm hf summable_of_summable_norm hg summable_mul_of_summable_norm hf hg

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`finset.range (n+1)` involving `nat` substraction.
In order to avoid `nat` substraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n`. -/


section Nat

open Finset.Nat

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `summable_norm_sum_mul_antidiagonal_of_summable_norm [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f `g] [":" (Term.arrow (termℕ "ℕ") "→" `α)] "}")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")))])]
     []
     ")")
    (Term.explicitBinder
     "("
     [`hg]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`x]) "∥")))])]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `Summable
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`n] [])]
        "=>"
        (Analysis.Normed.Group.Basic.«term∥_∥»
         "∥"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
          " in "
          (Term.app `antidiagonal [`n])
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
           "*"
           (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])))
         "∥")))])))
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
           []
           []
           ":="
           (Term.app
            `summable_sum_mul_antidiagonal_of_summable_mul
            [(Term.app
              `Summable.mul_of_nonneg
              [`hf
               `hg
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [(Term.hole "_")] [])]
                 "=>"
                 (Term.app `norm_nonneg [(Term.hole "_")])))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [(Term.hole "_")] [])]
                 "=>"
                 (Term.app `norm_nonneg [(Term.hole "_")])))])]))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `summable_of_nonneg_of_le
          [(Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
           (Term.hole "_")
           `this]))
        [])
       (group (Tactic.intro "intro" [`n]) [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_≤_»
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
              " in "
              (Term.app `antidiagonal [`n])
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
               "*"
               (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])))
             "∥")
            "≤"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
             " in "
             (Term.app `antidiagonal [`n])
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥»
              "∥"
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
               "*"
               (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]))
              "∥")))
           ":="
           (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
             " in "
             (Term.app `antidiagonal [`n])
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))]) "∥")
              "*"
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]) "∥"))))
           ":="
           (Term.app
            `sum_le_sum
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`i (Term.hole "_")] [])]
               "=>"
               (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")])))]))])
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
          []
          []
          ":="
          (Term.app
           `summable_sum_mul_antidiagonal_of_summable_mul
           [(Term.app
             `Summable.mul_of_nonneg
             [`hf
              `hg
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [(Term.hole "_")] [])]
                "=>"
                (Term.app `norm_nonneg [(Term.hole "_")])))
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [(Term.hole "_")] [])]
                "=>"
                (Term.app `norm_nonneg [(Term.hole "_")])))])]))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `summable_of_nonneg_of_le
         [(Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
          (Term.hole "_")
          `this]))
       [])
      (group (Tactic.intro "intro" [`n]) [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
             " in "
             (Term.app `antidiagonal [`n])
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
              "*"
              (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])))
            "∥")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
            " in "
            (Term.app `antidiagonal [`n])
            ", "
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
              "*"
              (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]))
             "∥")))
          ":="
          (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
            " in "
            (Term.app `antidiagonal [`n])
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))]) "∥")
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]) "∥"))))
          ":="
          (Term.app
           `sum_le_sum
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`i (Term.hole "_")] [])]
              "=>"
              (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")])))]))])
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
     («term_≤_»
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
        " in "
        (Term.app `antidiagonal [`n])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
         "*"
         (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])))
       "∥")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
       " in "
       (Term.app `antidiagonal [`n])
       ", "
       (Analysis.Normed.Group.Basic.«term∥_∥»
        "∥"
        (Finset.Data.Finset.Fold.«term_*_»
         (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
         "*"
         (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]))
        "∥")))
     ":="
     (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
       " in "
       (Term.app `antidiagonal [`n])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))]) "∥")
        "*"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]) "∥"))))
     ":="
     (Term.app
      `sum_le_sum
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`i (Term.hole "_")] [])]
         "=>"
         (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")])))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `sum_le_sum
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i (Term.hole "_")] [])]
      "=>"
      (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")])))])
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
    [(Term.simpleBinder [`i (Term.hole "_")] [])]
    "=>"
    (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")])
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
  `norm_mul_le
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_le_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
    " in "
    (Term.app `antidiagonal [`n])
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))]) "∥")
     "*"
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]) "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
   " in "
   (Term.app `antidiagonal [`n])
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))]) "∥")
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))]) "∥")
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `kl "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `kl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `kl "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `kl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `antidiagonal [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `antidiagonal
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
  summable_norm_sum_mul_antidiagonal_of_summable_norm
  { f g : ℕ → α } ( hf : Summable fun x => ∥ f x ∥ ) ( hg : Summable fun x => ∥ g x ∥ )
    : Summable fun n => ∥ ∑ kl in antidiagonal n , f kl . 1 * g kl . 2 ∥
  :=
    by
      have
          :=
            summable_sum_mul_antidiagonal_of_summable_mul
              Summable.mul_of_nonneg hf hg fun _ => norm_nonneg _ fun _ => norm_nonneg _
        refine' summable_of_nonneg_of_le fun _ => norm_nonneg _ _ this
        intro n
        calc
          ∥ ∑ kl in antidiagonal n , f kl . 1 * g kl . 2 ∥ ≤ ∑ kl in antidiagonal n , ∥ f kl . 1 * g kl . 2 ∥
              :=
              norm_sum_le _ _
            _ ≤ ∑ kl in antidiagonal n , ∥ f kl . 1 ∥ * ∥ g kl . 2 ∥ := sum_le_sum fun i _ => norm_mul_le _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,\n    expressed by summing on `finset.nat.antidiagonal`.\n    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are\n    *not* absolutely summable. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `CompleteSpace [`α]) "]")
    (Term.implicitBinder "{" [`f `g] [":" (Term.arrow (termℕ "ℕ") "→" `α)] "}")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")))])]
     []
     ")")
    (Term.explicitBinder
     "("
     [`hg]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`x]) "∥")))])]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
       ", "
       (Term.app `f [`n]))
      "*"
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
       ", "
       (Term.app `g [`n])))
     "="
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
      ", "
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
       " in "
       (Term.app `antidiagonal [`n])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
        "*"
        (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])))))))
  (Command.declValSimple
   ":="
   (Term.app
    `tsum_mul_tsum_eq_tsum_sum_antidiagonal
    [(Term.app `summable_of_summable_norm [`hf])
     (Term.app `summable_of_summable_norm [`hg])
     (Term.app `summable_mul_of_summable_norm [`hf `hg])])
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
   `tsum_mul_tsum_eq_tsum_sum_antidiagonal
   [(Term.app `summable_of_summable_norm [`hf])
    (Term.app `summable_of_summable_norm [`hg])
    (Term.app `summable_mul_of_summable_norm [`hf `hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `summable_mul_of_summable_norm [`hf `hg])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `summable_mul_of_summable_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `summable_mul_of_summable_norm [`hf `hg]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `summable_of_summable_norm [`hg])
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
  `summable_of_summable_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `summable_of_summable_norm [`hg]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `summable_of_summable_norm [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `summable_of_summable_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `summable_of_summable_norm [`hf]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
     ", "
     (Term.app `f [`n]))
    "*"
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
     ", "
     (Term.app `g [`n])))
   "="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
    ", "
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
     " in "
     (Term.app `antidiagonal [`n])
     ", "
     (Finset.Data.Finset.Fold.«term_*_»
      (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
      "*"
      (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   ", "
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
    " in "
    (Term.app `antidiagonal [`n])
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
     "*"
     (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `kl)] []))
   " in "
   (Term.app `antidiagonal [`n])
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
    "*"
    (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
   "*"
   (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [(Term.proj `kl "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `kl "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `kl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `f [(Term.proj `kl "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `kl "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `kl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `antidiagonal [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `antidiagonal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
        expressed by summing on `finset.nat.antidiagonal`.
        See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
        *not* absolutely summable. -/
  theorem
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    [ CompleteSpace α ] { f g : ℕ → α } ( hf : Summable fun x => ∥ f x ∥ ) ( hg : Summable fun x => ∥ g x ∥ )
      : ∑' n , f n * ∑' n , g n = ∑' n , ∑ kl in antidiagonal n , f kl . 1 * g kl . 2
    :=
      tsum_mul_tsum_eq_tsum_sum_antidiagonal
        summable_of_summable_norm hf summable_of_summable_norm hg summable_mul_of_summable_norm hf hg

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `summable_norm_sum_mul_range_of_summable_norm [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f `g] [":" (Term.arrow (termℕ "ℕ") "→" `α)] "}")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")))])]
     []
     ")")
    (Term.explicitBinder
     "("
     [`hg]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`x]) "∥")))])]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `Summable
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`n] [])]
        "=>"
        (Analysis.Normed.Group.Basic.«term∥_∥»
         "∥"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
          " in "
          (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
          ", "
          (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)])))
         "∥")))])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simpRw
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            ["←"]
            (Term.app
             `sum_antidiagonal_eq_sum_range_succ
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`k `l] [])]
                "=>"
                (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))]))]
          "]")
         [])
        [])
       (group (Tactic.exact "exact" (Term.app `summable_norm_sum_mul_antidiagonal_of_summable_norm [`hf `hg])) [])])))
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
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.app
            `sum_antidiagonal_eq_sum_range_succ
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k `l] [])]
               "=>"
               (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))]))]
         "]")
        [])
       [])
      (group (Tactic.exact "exact" (Term.app `summable_norm_sum_mul_antidiagonal_of_summable_norm [`hf `hg])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `summable_norm_sum_mul_antidiagonal_of_summable_norm [`hf `hg]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `summable_norm_sum_mul_antidiagonal_of_summable_norm [`hf `hg])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `summable_norm_sum_mul_antidiagonal_of_summable_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simpRw
   "simp_rw"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      ["←"]
      (Term.app
       `sum_antidiagonal_eq_sum_range_succ
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k `l] [])]
          "=>"
          (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `sum_antidiagonal_eq_sum_range_succ
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`k `l] [])]
      "=>"
      (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))])
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
    [(Term.simpleBinder [`k `l] [])]
    "=>"
    (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `f [`k])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
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
  `sum_antidiagonal_eq_sum_range_succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `Summable
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`n] [])]
      "=>"
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)])))
       "∥")))])
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
    [(Term.simpleBinder [`n] [])]
    "=>"
    (Analysis.Normed.Group.Basic.«term∥_∥»
     "∥"
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
      " in "
      (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
      ", "
      (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)])))
     "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥»
   "∥"
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
    " in "
    (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
    ", "
    (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)])))
   "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
   " in "
   (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
   ", "
   (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [(«term_-_» `n "-" `k)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `n "-" `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `n "-" `k) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `f [`k])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
  summable_norm_sum_mul_range_of_summable_norm
  { f g : ℕ → α } ( hf : Summable fun x => ∥ f x ∥ ) ( hg : Summable fun x => ∥ g x ∥ )
    : Summable fun n => ∥ ∑ k in range n + 1 , f k * g n - k ∥
  :=
    by
      simp_rw [ ← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l ]
        exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,\n    expressed by summing on `finset.range`.\n    See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are\n    *not* absolutely summable. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `CompleteSpace [`α]) "]")
    (Term.implicitBinder "{" [`f `g] [":" (Term.arrow (termℕ "ℕ") "→" `α)] "}")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `f [`x]) "∥")))])]
     []
     ")")
    (Term.explicitBinder
     "("
     [`hg]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `g [`x]) "∥")))])]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
       ", "
       (Term.app `f [`n]))
      "*"
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
       ", "
       (Term.app `g [`n])))
     "="
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
      ", "
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       " in "
       (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
       ", "
       (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)])))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simpRw
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            ["←"]
            (Term.app
             `sum_antidiagonal_eq_sum_range_succ
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`k `l] [])]
                "=>"
                (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))]))]
          "]")
         [])
        [])
       (group
        (Tactic.exact "exact" (Term.app `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [`hf `hg]))
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
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.app
            `sum_antidiagonal_eq_sum_range_succ
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k `l] [])]
               "=>"
               (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))]))]
         "]")
        [])
       [])
      (group
       (Tactic.exact "exact" (Term.app `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [`hf `hg]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [`hf `hg]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [`hf `hg])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simpRw
   "simp_rw"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      ["←"]
      (Term.app
       `sum_antidiagonal_eq_sum_range_succ
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k `l] [])]
          "=>"
          (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `sum_antidiagonal_eq_sum_range_succ
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`k `l] [])]
      "=>"
      (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))])
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
    [(Term.simpleBinder [`k `l] [])]
    "=>"
    (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [`l]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `f [`k])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
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
  `sum_antidiagonal_eq_sum_range_succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
     ", "
     (Term.app `f [`n]))
    "*"
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
     ", "
     (Term.app `g [`n])))
   "="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
    ", "
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
     " in "
     (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
     ", "
     (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   ", "
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
    " in "
    (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
    ", "
    (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
   " in "
   (Term.app `range [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
   ", "
   (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`k]) "*" (Term.app `g [(«term_-_» `n "-" `k)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [(«term_-_» `n "-" `k)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» `n "-" `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `n "-" `k) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `f [`k])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
        expressed by summing on `finset.range`.
        See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
        *not* absolutely summable. -/
  theorem
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    [ CompleteSpace α ] { f g : ℕ → α } ( hf : Summable fun x => ∥ f x ∥ ) ( hg : Summable fun x => ∥ g x ∥ )
      : ∑' n , f n * ∑' n , g n = ∑' n , ∑ k in range n + 1 , f k * g n - k
    :=
      by
        simp_rw [ ← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l ]
          exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg

end Nat

end CauchyProduct

section RingHomIsometric

variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}

/--  This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
class RingHomIsometric [Semiringₓ R₁] [Semiringₓ R₂] [HasNorm R₁] [HasNorm R₂] (σ : R₁ →+* R₂) : Prop where
  IsIso : ∀ {x : R₁}, ∥σ x∥ = ∥x∥

attribute [simp] RingHomIsometric.is_iso

variable [SemiNormedRing R₁] [SemiNormedRing R₂] [SemiNormedRing R₃]

instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨fun x => rfl⟩

end RingHomIsometric

