/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Order.Disjoint
import Mathbin.Order.WithBot

/-!

# The order on `Prop`

Instances on `Prop` such as `distrib_lattice`, `bounded_order`, `linear_order`.

-/


/-- Propositions form a distributive lattice. -/
instance PropCat.distribLattice : DistribLattice Prop :=
  { PropCat.partialOrder with sup := Or, le_sup_left := @Or.inl, le_sup_right := @Or.inr,
    sup_le := fun a b c => Or.ndrec, inf := And, inf_le_left := @And.left, inf_le_right := @And.right,
    le_inf := fun a b c Hab Hac Ha => And.intro (Hab Ha) (Hac Ha), le_sup_inf := fun a b c => or_and_left.2 }
#align Prop.distrib_lattice PropCat.distribLattice

/-- Propositions form a bounded order. -/
instance PropCat.boundedOrder : BoundedOrder Prop where
  top := True
  le_top a Ha := True.intro
  bot := False
  bot_le := @False.elim
#align Prop.bounded_order PropCat.boundedOrder

theorem PropCat.bot_eq_false : (⊥ : Prop) = False :=
  rfl
#align Prop.bot_eq_false PropCat.bot_eq_false

theorem PropCat.top_eq_true : (⊤ : Prop) = True :=
  rfl
#align Prop.top_eq_true PropCat.top_eq_true

instance PropCat.le_is_total : IsTotal Prop (· ≤ ·) :=
  ⟨fun p q => by
    change (p → q) ∨ (q → p)
    tauto!⟩
#align Prop.le_is_total PropCat.le_is_total

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [(Command.noncomputable "noncomputable")] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `PropCat.linearOrder [])]
      (Command.declSig [] (Term.typeSpec ":" (Term.app `LinearOrder [(Term.prop "Prop")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact "exact" (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact "exact" (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact "exact" (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lattice.toLinearOrder [(Term.prop "Prop")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.prop', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.prop', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.prop "Prop")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lattice.toLinearOrder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
noncomputable instance PropCat.linearOrder : LinearOrder Prop := by skip <;> exact Lattice.toLinearOrder Prop
#align Prop.linear_order PropCat.linearOrder

@[simp]
theorem sup_Prop_eq : (· ⊔ ·) = (· ∨ ·) :=
  rfl
#align sup_Prop_eq sup_Prop_eq

@[simp]
theorem inf_Prop_eq : (· ⊓ ·) = (· ∧ ·) :=
  rfl
#align inf_Prop_eq inf_Prop_eq

namespace Pi

variable {ι : Type _} {α' : ι → Type _} [∀ i, PartialOrder (α' i)]

theorem disjoint_iff [∀ i, OrderBot (α' i)] {f g : ∀ i, α' i} : Disjoint f g ↔ ∀ i, Disjoint (f i) (g i) := by
  constructor
  · intro h i x hf hg
    refine'
      (update_le_iff.mp <|-- this line doesn't work
            h
            (update_le_iff.mpr ⟨hf, fun _ _ => _⟩) (update_le_iff.mpr ⟨hg, fun _ _ => _⟩)).1
    · exact ⊥
      
    · exact bot_le
      
    · exact bot_le
      
    
  · intro h x hf hg i
    apply h i (hf i) (hg i)
    
#align pi.disjoint_iff Pi.disjoint_iff

theorem codisjoint_iff [∀ i, OrderTop (α' i)] {f g : ∀ i, α' i} : Codisjoint f g ↔ ∀ i, Codisjoint (f i) (g i) :=
  @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _
#align pi.codisjoint_iff Pi.codisjoint_iff

theorem is_compl_iff [∀ i, BoundedOrder (α' i)] {f g : ∀ i, α' i} : IsCompl f g ↔ ∀ i, IsCompl (f i) (g i) := by
  simp_rw [is_compl_iff, disjoint_iff, codisjoint_iff, forall_and]
#align pi.is_compl_iff Pi.is_compl_iff

end Pi

@[simp]
theorem PropCat.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q) :=
  disjoint_iff_inf_le
#align Prop.disjoint_iff PropCat.disjoint_iff

@[simp]
theorem PropCat.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q :=
  codisjoint_iff_le_sup.trans <| forall_const _
#align Prop.codisjoint_iff PropCat.codisjoint_iff

@[simp]
theorem PropCat.is_compl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q) := by
  rw [is_compl_iff, PropCat.disjoint_iff, PropCat.codisjoint_iff, not_iff]
  tauto
#align Prop.is_compl_iff PropCat.is_compl_iff

