import Mathbin.Data.Equiv.Basic
import Mathbin.Data.Equiv.Option
import Mathbin.Dynamics.FixedPoints.Basic
import Mathbin.GroupTheory.Perm.Option

/-!
# Derangements on types

In this file we define `derangements α`, the set of derangements on a type `α`.

We also define some equivalences involving various subtypes of `perm α` and `derangements α`:
* `derangements_option_equiv_sigma_at_most_one_fixed_point`: An equivalence between
  `derangements (option α)` and the sigma-type `Σ a : α, {f : perm α // fixed_points f ⊆ a}`.
* `derangements_recursion_equiv`: An equivalence between `derangements (option α)` and the
  sigma-type `Σ a : α, (derangements (({a}ᶜ : set α) : Type _) ⊕ derangements α)` which is later
  used to inductively count the number of derangements.

In order to prove the above, we also prove some results about the effect of `equiv.remove_none`
on derangements: `remove_none.fiber_none` and `remove_none.fiber_some`.
-/


open Equivₓ Function

/--  A permutation is a derangement if it has no fixed points. -/
def Derangements (α : Type _) : Set (perm α) :=
  { f : perm α | ∀ x : α, f x ≠ x }

variable {α β : Type _}

theorem mem_derangements_iff_fixed_points_eq_empty {f : perm α} : f ∈ Derangements α ↔ fixed_points f = ∅ :=
  Set.eq_empty_iff_forall_not_mem.symm

/--  If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
def Equivₓ.derangementsCongr (e : α ≃ β) : Derangements α ≃ Derangements β :=
  e.perm_congr.subtype_equiv $ fun f =>
    e.forall_congr $ by
      simp

namespace Derangements

/--  Derangements on a subtype are equivalent to permutations on the original type where points are
fixed iff they are not in the subtype. -/
protected def subtype_equiv (p : α → Prop) [DecidablePred p] :
    Derangements (Subtype p) ≃ { f : perm α // ∀ a, ¬p a ↔ a ∈ fixed_points f } :=
  calc
    Derangements (Subtype p) ≃
      { f : { f : perm α // ∀ a, ¬p a → a ∈ fixed_points f } // ∀ a, a ∈ fixed_points f → ¬p a } :=
    by
    refine' (perm.subtype_equiv_subtype_perm p).subtypeEquiv fun f => ⟨fun hf a hfa ha => _, _⟩
    ·
      refine' hf ⟨a, ha⟩ (Subtype.ext _)
      rwa [mem_fixed_points, is_fixed_pt, perm.subtype_equiv_subtype_perm, @coe_fn_coe_base', Equivₓ.coe_fn_mk,
        Subtype.coe_mk, Equivₓ.Perm.of_subtype_apply_of_mem] at hfa
    rintro hf ⟨a, ha⟩ hfa
    refine' hf _ _ ha
    change perm.subtype_equiv_subtype_perm p f a = a
    rw [perm.subtype_equiv_subtype_perm_apply_of_mem f ha, hfa, Subtype.coe_mk]
    _ ≃ { f : perm α // ∃ h : ∀ a, ¬p a → a ∈ fixed_points f, ∀ a, a ∈ fixed_points f → ¬p a } :=
    subtype_subtype_equiv_subtype_exists _ _
    _ ≃ { f : perm α // ∀ a, ¬p a ↔ a ∈ fixed_points f } :=
    subtype_equiv_right fun f => by
      simp_rw [exists_prop, ← forall_and_distrib, ← iff_iff_implies_and_implies]
    

/--  The set of permutations that fix either `a` or nothing is equivalent to the sum of:
    - derangements on `α`
    - derangements on `α` minus `a`. -/
def at_most_one_fixed_point_equiv_sum_derangements [DecidableEq α] (a : α) :
    { f : perm α // fixed_points f ⊆ {a} } ≃ Sum (Derangements ({a}ᶜ : Set α)) (Derangements α) :=
  calc
    { f : perm α // fixed_points f ⊆ {a} } ≃
      Sum { f : { f : perm α // fixed_points f ⊆ {a} } // a ∈ fixed_points f }
        { f : { f : perm α // fixed_points f ⊆ {a} } // a ∉ fixed_points f } :=
    (Equivₓ.sumCompl _).symm
    _ ≃
      Sum { f : perm α // fixed_points f ⊆ {a} ∧ a ∈ fixed_points f }
        { f : perm α // fixed_points f ⊆ {a} ∧ a ∉ fixed_points f } :=
    by
    refine' Equivₓ.sumCongr _ _ <;>
      ·
        convert subtype_subtype_equiv_subtype_inter _ _
        ext f
        rfl
    _ ≃ Sum { f : perm α // fixed_points f = {a} } { f : perm α // fixed_points f = ∅ } := by
    refine' Equivₓ.sumCongr (subtype_equiv_right $ fun f => _) (subtype_equiv_right $ fun f => _)
    ·
      rw [Set.eq_singleton_iff_unique_mem, and_comm]
      rfl
    ·
      rw [Set.eq_empty_iff_forall_not_mem]
      refine' ⟨fun h x hx => h.2 (h.1 hx ▸ hx), fun h => ⟨fun x hx => (h _ hx).elim, h _⟩⟩
    _ ≃ Sum (Derangements ({a}ᶜ : Set α)) (Derangements α) := by
    refine'
      Equivₓ.sumCongr ((Derangements.subtypeEquiv _).trans $ subtype_equiv_right $ fun x => _).symm
        (subtype_equiv_right $ fun f => mem_derangements_iff_fixed_points_eq_empty.symm)
    rw [eq_comm, Set.ext_iff]
    simp_rw [Set.mem_compl_iff, not_not]
    

namespace Equivₓ

variable [DecidableEq α]

/--  The set of permutations `f` such that the preimage of `(a, f)` under
    `equiv.perm.decompose_option` is a derangement. -/
def remove_none.fiber (a : Option α) : Set (perm α) :=
  { f : perm α | (a, f) ∈ Equivₓ.Perm.decomposeOption '' Derangements (Option α) }

theorem remove_none.mem_fiber (a : Option α) (f : perm α) :
    f ∈ remove_none.fiber a ↔ ∃ F : perm (Option α), F ∈ Derangements (Option α) ∧ F none = a ∧ remove_none F = f := by
  simp [remove_none.fiber, Derangements]

theorem remove_none.fiber_none : remove_none.fiber (@none α) = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro f hyp
  rw [remove_none.mem_fiber] at hyp
  rcases hyp with ⟨F, F_derangement, F_none, _⟩
  exact F_derangement none F_none

/--  For any `a : α`, the fiber over `some a` is the set of permutations
    where `a` is the only possible fixed point. -/
theorem remove_none.fiber_some (a : α) : remove_none.fiber (some a) = { f : perm α | fixed_points f ⊆ {a} } := by
  ext f
  constructor
  ·
    rw [remove_none.mem_fiber]
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed
    rw [mem_fixed_points_iff] at x_fixed
    apply_fun some  at x_fixed
    cases' Fx : F (some x) with y
    ·
      rwa [remove_none_none F Fx, F_none, Option.some_inj, eq_comm] at x_fixed
    ·
      exfalso
      rw [remove_none_some F ⟨y, Fx⟩] at x_fixed
      exact F_derangement _ x_fixed
  ·
    intro h_opfp
    use equiv.perm.decompose_option.symm (some a, f)
    constructor
    ·
      intro x
      apply_fun swap none (some a)
      simp only [perm.decompose_option_symm_apply, swap_apply_self, perm.coe_mul]
      cases x
      ·
        simp
      simp only [EquivFunctor.map_equiv_apply, EquivFunctor.map, Option.map_eq_map, Option.map_some'ₓ]
      by_cases' x_vs_a : x = a
      ·
        rw [x_vs_a, swap_apply_right]
        apply Option.some_ne_none
      have ne_1 : some x ≠ none := Option.some_ne_none _
      have ne_2 : some x ≠ some a := (Option.some_injective α).ne_iff.mpr x_vs_a
      rw [swap_apply_of_ne_of_ne ne_1 ne_2, (Option.some_injective α).ne_iff]
      intro contra
      exact x_vs_a (h_opfp contra)
    ·
      rw [apply_symm_apply]

end Equivₓ

section Option

variable [DecidableEq α]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The set of derangements on `option α` is equivalent to the union over `a : α`\n    of \"permutations with `a` the only possible fixed point\". -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `derangements_option_equiv_sigma_at_most_one_fixed_point [])
  (Command.optDeclSig
   []
   [(Term.typeSpec
     ":"
     (Data.Equiv.Basic.«term_≃_»
      (Term.app `Derangements [(Term.app `Option [`α])])
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
       ", "
       (Set.«term{_|_}»
        "{"
        (Mathlib.ExtendedBinder.extBinder `f [":" (Term.app `perm [`α])])
        "|"
        (Init.Core.«term_⊆_» (Term.app `fixed_points [`f]) " ⊆ " (Set.«term{_}» "{" [`a] "}"))
        "}"))))])
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
           [`fiber_none_is_false []]
           [(Term.typeSpec
             ":"
             (Term.arrow (Term.app `equiv.remove_none.fiber [(Term.app (Term.explicit "@" `none) [`α])]) "→" `False))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `equiv.remove_none.fiber_none)] "]") [])
                [])
               (group (Tactic.exact "exact" `IsEmpty.false) [])]))))))
        [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           (Data.Equiv.Basic.«term_≃_»
            (Term.app `Derangements [(Term.app `Option [`α])])
            " ≃ "
            (Set.Data.Set.Basic.term_''_
             `Equivₓ.Perm.decomposeOption
             " '' "
             (Term.app `Derangements [(Term.app `Option [`α])])))
           ":="
           (Term.app `Equivₓ.image [(Term.hole "_") (Term.hole "_")]))
          (calcStep
           (Data.Equiv.Basic.«term_≃_»
            (Term.hole "_")
            " ≃ "
            (Init.Data.Sigma.Basic.«termΣ_,_»
             "Σ"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" (Term.app `Option [`α])]))
             ", "
             (Init.Coe.«term↥_» "↥" (Term.app `equiv.remove_none.fiber [`a]))))
           ":="
           (Term.app `set_prod_equiv_sigma [(Term.hole "_")]))
          (calcStep
           (Data.Equiv.Basic.«term_≃_»
            (Term.hole "_")
            " ≃ "
            (Init.Data.Sigma.Basic.«termΣ_,_»
             "Σ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
             ", "
             (Init.Coe.«term↥_» "↥" (Term.app `equiv.remove_none.fiber [(Term.app `some [`a])]))))
           ":="
           (Term.app `sigma_option_equiv_of_some [(Term.hole "_") `fiber_none_is_false]))
          (calcStep
           (Data.Equiv.Basic.«term_≃_»
            (Term.hole "_")
            " ≃ "
            (Init.Data.Sigma.Basic.«termΣ_,_»
             "Σ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
             ", "
             (Set.«term{_|_}»
              "{"
              (Mathlib.ExtendedBinder.extBinder `f [":" (Term.app `perm [`α])])
              "|"
              (Init.Core.«term_⊆_» (Term.app `fixed_points [`f]) " ⊆ " (Set.«term{_}» "{" [`a] "}"))
              "}")))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simpRw
                 "simp_rw"
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `equiv.remove_none.fiber_some)] "]")
                 [])
                [])]))))])
        [])])))
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`fiber_none_is_false []]
          [(Term.typeSpec
            ":"
            (Term.arrow (Term.app `equiv.remove_none.fiber [(Term.app (Term.explicit "@" `none) [`α])]) "→" `False))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `equiv.remove_none.fiber_none)] "]") [])
               [])
              (group (Tactic.exact "exact" `IsEmpty.false) [])]))))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          (Data.Equiv.Basic.«term_≃_»
           (Term.app `Derangements [(Term.app `Option [`α])])
           " ≃ "
           (Set.Data.Set.Basic.term_''_
            `Equivₓ.Perm.decomposeOption
            " '' "
            (Term.app `Derangements [(Term.app `Option [`α])])))
          ":="
          (Term.app `Equivₓ.image [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          (Data.Equiv.Basic.«term_≃_»
           (Term.hole "_")
           " ≃ "
           (Init.Data.Sigma.Basic.«termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" (Term.app `Option [`α])]))
            ", "
            (Init.Coe.«term↥_» "↥" (Term.app `equiv.remove_none.fiber [`a]))))
          ":="
          (Term.app `set_prod_equiv_sigma [(Term.hole "_")]))
         (calcStep
          (Data.Equiv.Basic.«term_≃_»
           (Term.hole "_")
           " ≃ "
           (Init.Data.Sigma.Basic.«termΣ_,_»
            "Σ"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
            ", "
            (Init.Coe.«term↥_» "↥" (Term.app `equiv.remove_none.fiber [(Term.app `some [`a])]))))
          ":="
          (Term.app `sigma_option_equiv_of_some [(Term.hole "_") `fiber_none_is_false]))
         (calcStep
          (Data.Equiv.Basic.«term_≃_»
           (Term.hole "_")
           " ≃ "
           (Init.Data.Sigma.Basic.«termΣ_,_»
            "Σ"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
            ", "
            (Set.«term{_|_}»
             "{"
             (Mathlib.ExtendedBinder.extBinder `f [":" (Term.app `perm [`α])])
             "|"
             (Init.Core.«term_⊆_» (Term.app `fixed_points [`f]) " ⊆ " (Set.«term{_}» "{" [`a] "}"))
             "}")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simpRw
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `equiv.remove_none.fiber_some)] "]")
                [])
               [])]))))])
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
     (Data.Equiv.Basic.«term_≃_»
      (Term.app `Derangements [(Term.app `Option [`α])])
      " ≃ "
      (Set.Data.Set.Basic.term_''_
       `Equivₓ.Perm.decomposeOption
       " '' "
       (Term.app `Derangements [(Term.app `Option [`α])])))
     ":="
     (Term.app `Equivₓ.image [(Term.hole "_") (Term.hole "_")]))
    (calcStep
     (Data.Equiv.Basic.«term_≃_»
      (Term.hole "_")
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" (Term.app `Option [`α])]))
       ", "
       (Init.Coe.«term↥_» "↥" (Term.app `equiv.remove_none.fiber [`a]))))
     ":="
     (Term.app `set_prod_equiv_sigma [(Term.hole "_")]))
    (calcStep
     (Data.Equiv.Basic.«term_≃_»
      (Term.hole "_")
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
       ", "
       (Init.Coe.«term↥_» "↥" (Term.app `equiv.remove_none.fiber [(Term.app `some [`a])]))))
     ":="
     (Term.app `sigma_option_equiv_of_some [(Term.hole "_") `fiber_none_is_false]))
    (calcStep
     (Data.Equiv.Basic.«term_≃_»
      (Term.hole "_")
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
       ", "
       (Set.«term{_|_}»
        "{"
        (Mathlib.ExtendedBinder.extBinder `f [":" (Term.app `perm [`α])])
        "|"
        (Init.Core.«term_⊆_» (Term.app `fixed_points [`f]) " ⊆ " (Set.«term{_}» "{" [`a] "}"))
        "}")))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `equiv.remove_none.fiber_some)] "]") [])
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `equiv.remove_none.fiber_some)] "]") [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `equiv.remove_none.fiber_some)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `equiv.remove_none.fiber_some
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Equiv.Basic.«term_≃_»
   (Term.hole "_")
   " ≃ "
   (Init.Data.Sigma.Basic.«termΣ_,_»
    "Σ"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
    ", "
    (Set.«term{_|_}»
     "{"
     (Mathlib.ExtendedBinder.extBinder `f [":" (Term.app `perm [`α])])
     "|"
     (Init.Core.«term_⊆_» (Term.app `fixed_points [`f]) " ⊆ " (Set.«term{_}» "{" [`a] "}"))
     "}")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Equiv.Basic.«term_≃_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
   ", "
   (Set.«term{_|_}»
    "{"
    (Mathlib.ExtendedBinder.extBinder `f [":" (Term.app `perm [`α])])
    "|"
    (Init.Core.«term_⊆_» (Term.app `fixed_points [`f]) " ⊆ " (Set.«term{_}» "{" [`a] "}"))
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   (Mathlib.ExtendedBinder.extBinder `f [":" (Term.app `perm [`α])])
   "|"
   (Init.Core.«term_⊆_» (Term.app `fixed_points [`f]) " ⊆ " (Set.«term{_}» "{" [`a] "}"))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_⊆_» (Term.app `fixed_points [`f]) " ⊆ " (Set.«term{_}» "{" [`a] "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_}» "{" [`a] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `fixed_points [`f])
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
  `fixed_points
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `perm [`α])
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
  `perm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
    The set of derangements on `option α` is equivalent to the union over `a : α`
        of "permutations with `a` the only possible fixed point". -/
  def
    derangements_option_equiv_sigma_at_most_one_fixed_point
    : Derangements Option α ≃ Σ a : α , { f : perm α | fixed_points f ⊆ { a } }
    :=
      by
        have
            fiber_none_is_false
              : equiv.remove_none.fiber @ none α → False
              :=
              by rw [ equiv.remove_none.fiber_none ] exact IsEmpty.false
          calc
            Derangements Option α ≃ Equivₓ.Perm.decomposeOption '' Derangements Option α := Equivₓ.image _ _
              _ ≃ Σ a : Option α , ↥ equiv.remove_none.fiber a := set_prod_equiv_sigma _
              _ ≃ Σ a : α , ↥ equiv.remove_none.fiber some a := sigma_option_equiv_of_some _ fiber_none_is_false
              _ ≃ Σ a : α , { f : perm α | fixed_points f ⊆ { a } } := by simp_rw [ equiv.remove_none.fiber_some ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The set of derangements on `option α` is equivalent to the union over all `a : α` of\n    \"derangements on `α` ⊕ derangements on `{a}ᶜ`\". -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `derangements_recursion_equiv [])
  (Command.optDeclSig
   []
   [(Term.typeSpec
     ":"
     (Data.Equiv.Basic.«term_≃_»
      (Term.app `Derangements [(Term.app `Option [`α])])
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
       ", "
       (Term.app
        `Sum
        [(Term.app
          `Derangements
          [(Term.paren
            "("
            [(Term.paren
              "("
              [(Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ")
               [(Term.typeAscription ":" (Term.app `Set [`α]))]]
              ")")
             [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]]
            ")")])
         (Term.app `Derangements [`α])]))))])
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj `derangements_option_equiv_sigma_at_most_one_fixed_point "." `trans)
    [(Term.app `sigma_congr_right [`at_most_one_fixed_point_equiv_sum_derangements])])
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
  (Term.app
   (Term.proj `derangements_option_equiv_sigma_at_most_one_fixed_point "." `trans)
   [(Term.app `sigma_congr_right [`at_most_one_fixed_point_equiv_sum_derangements])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sigma_congr_right [`at_most_one_fixed_point_equiv_sum_derangements])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `at_most_one_fixed_point_equiv_sum_derangements
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sigma_congr_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `sigma_congr_right [`at_most_one_fixed_point_equiv_sum_derangements]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `derangements_option_equiv_sigma_at_most_one_fixed_point "." `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `derangements_option_equiv_sigma_at_most_one_fixed_point
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Data.Equiv.Basic.«term_≃_»
   (Term.app `Derangements [(Term.app `Option [`α])])
   " ≃ "
   (Init.Data.Sigma.Basic.«termΣ_,_»
    "Σ"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
    ", "
    (Term.app
     `Sum
     [(Term.app
       `Derangements
       [(Term.paren
         "("
         [(Term.paren
           "("
           [(Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ")
            [(Term.typeAscription ":" (Term.app `Set [`α]))]]
           ")")
          [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]]
         ")")])
      (Term.app `Derangements [`α])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Equiv.Basic.«term_≃_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
   ", "
   (Term.app
    `Sum
    [(Term.app
      `Derangements
      [(Term.paren
        "("
        [(Term.paren
          "("
          [(Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ")
           [(Term.typeAscription ":" (Term.app `Set [`α]))]]
          ")")
         [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]]
        ")")])
     (Term.app `Derangements [`α])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Sum
   [(Term.app
     `Derangements
     [(Term.paren
       "("
       [(Term.paren
         "("
         [(Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ")
          [(Term.typeAscription ":" (Term.app `Set [`α]))]]
         ")")
        [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]]
       ")")])
    (Term.app `Derangements [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Derangements [`α])
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
  `Derangements
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Derangements [`α]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `Derangements
   [(Term.paren
     "("
     [(Term.paren
       "("
       [(Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ")
        [(Term.typeAscription ":" (Term.app `Set [`α]))]]
       ")")
      [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]]
     ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Term.paren
     "("
     [(Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ") [(Term.typeAscription ":" (Term.app `Set [`α]))]]
     ")")
    [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.type "Type" [(Level.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.type', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.type', expected 'Lean.Parser.Term.type.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Level.hole', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Level.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Level.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Level.hole', expected 'Lean.Parser.Level.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1024, level) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.paren
   "("
   [(Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ") [(Term.typeAscription ":" (Term.app `Set [`α]))]]
   ")")
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
  (Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BooleanAlgebra.«term_ᶜ»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 999, term))
  (Set.«term{_}» "{" [`a] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (some 999, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 999, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Derangements
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Derangements
   [(Term.paren
     "("
     [(Term.paren
       "("
       [(Order.BooleanAlgebra.«term_ᶜ» (Set.«term{_}» "{" [`a] "}") "ᶜ")
        [(Term.typeAscription ":" (Term.app `Set [`α]))]]
       ")")
      [(Term.typeAscription ":" (Term.type "Type" [(Level.hole "_")]))]]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    The set of derangements on `option α` is equivalent to the union over all `a : α` of
        "derangements on `α` ⊕ derangements on `{a}ᶜ`". -/
  def
    derangements_recursion_equiv
    : Derangements Option α ≃ Σ a : α , Sum Derangements ( ( { a } ᶜ : Set α ) : Type _ ) Derangements α
    :=
      derangements_option_equiv_sigma_at_most_one_fixed_point . trans
        sigma_congr_right at_most_one_fixed_point_equiv_sum_derangements

end Option

end Derangements

