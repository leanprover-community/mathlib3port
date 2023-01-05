/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning

! This file was ported from Lean 3 source module group_theory.group_action.quotient
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Dynamics.PeriodicPts
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.Commutator
import Mathbin.GroupTheory.Coset

/-!
# Properties of group actions involving quotient groups

This file proves properties of group actions which use the quotient group construction, notably
* the orbit-stabilizer theorem `card_orbit_mul_card_stabilizer_eq_card_group`
* the class formula `card_eq_sum_card_group_div_card_stabilizer'`
* Burnside's lemma `sum_card_fixed_by_eq_card_orbits_mul_card_group`
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

open BigOperators

namespace MulAction

variable [Group α]

section QuotientAction

open Subgroup MulOpposite QuotientGroup

variable (β) [Monoid β] [MulAction β α] (H : Subgroup α)

/-- A typeclass for when a `mul_action β α` descends to the quotient `α ⧸ H`. -/
class QuotientAction : Prop where
  inv_mul_mem : ∀ (b : β) {a a' : α}, a⁻¹ * a' ∈ H → (b • a)⁻¹ * b • a' ∈ H
#align mul_action.quotient_action MulAction.QuotientAction

/-- A typeclass for when an `add_action β α` descends to the quotient `α ⧸ H`. -/
class AddAction.QuotientAction {α : Type _} (β : Type _) [AddGroup α] [AddMonoid β] [AddAction β α]
  (H : AddSubgroup α) : Prop where
  inv_mul_mem : ∀ (b : β) {a a' : α}, -a + a' ∈ H → -(b +ᵥ a) + (b +ᵥ a') ∈ H
#align add_action.quotient_action AddAction.QuotientAction

attribute [to_additive AddAction.QuotientAction] MulAction.QuotientAction

@[to_additive]
instance left_quotient_action : QuotientAction α H :=
  ⟨fun _ _ _ _ => by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩
#align mul_action.left_quotient_action MulAction.left_quotient_action

@[to_additive]
instance right_quotient_action : QuotientAction H.normalizer.opposite H :=
  ⟨fun b c _ _ => by
    rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ← mul_assoc,
      mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩
#align mul_action.right_quotient_action MulAction.right_quotient_action

@[to_additive]
instance right_quotient_action' [hH : H.Normal] : QuotientAction αᵐᵒᵖ H :=
  ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff, mul_assoc,
      mul_inv_cancel_right]⟩
#align mul_action.right_quotient_action' MulAction.right_quotient_action'

@[to_additive]
instance quotient [QuotientAction β H] : MulAction β (α ⧸ H)
    where
  smul b :=
    Quotient.map' ((· • ·) b) fun a a' h =>
      left_rel_apply.mpr <| QuotientAction.inv_mul_mem b <| left_rel_apply.mp h
  one_smul q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk' (one_smul β a)
  mul_smul b b' q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk' (mul_smul b b' a)
#align mul_action.quotient MulAction.quotient

variable {β}

@[simp, to_additive]
theorem quotient.smul_mk [QuotientAction β H] (b : β) (a : α) :
    (b • QuotientGroup.mk a : α ⧸ H) = QuotientGroup.mk (b • a) :=
  rfl
#align mul_action.quotient.smul_mk MulAction.quotient.smul_mk

@[simp, to_additive]
theorem quotient.smul_coe [QuotientAction β H] (b : β) (a : α) : (b • a : α ⧸ H) = ↑(b • a) :=
  rfl
#align mul_action.quotient.smul_coe MulAction.quotient.smul_coe

@[simp, to_additive]
theorem quotient.mk_smul_out' [QuotientAction β H] (b : β) (q : α ⧸ H) :
    QuotientGroup.mk (b • q.out') = b • q := by rw [← quotient.smul_mk, QuotientGroup.out_eq']
#align mul_action.quotient.mk_smul_out' MulAction.quotient.mk_smul_out'

@[simp, to_additive]
theorem quotient.coe_smul_out' [QuotientAction β H] (b : β) (q : α ⧸ H) : ↑(b • q.out') = b • q :=
  quotient.mk_smul_out' H b q
#align mul_action.quotient.coe_smul_out' MulAction.quotient.coe_smul_out'

theorem QuotientGroup.out'_conj_pow_minimal_period_mem (a : α) (q : α ⧸ H) :
    q.out'⁻¹ * a ^ Function.minimalPeriod ((· • ·) a) q * q.out' ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq', QuotientGroup.out_eq', ← smul_eq_mul, quotient.mk_smul_out',
    eq_comm, pow_smul_eq_iff_minimal_period_dvd]
#align
  quotient_group.out'_conj_pow_minimal_period_mem QuotientGroup.out'_conj_pow_minimal_period_mem

end QuotientAction

open QuotientGroup

/-- The canonical map to the left cosets. -/
def MulActionHom.toQuotient (H : Subgroup α) : α →[α] α ⧸ H :=
  ⟨coe, quotient.smul_coe H⟩
#align mul_action_hom.to_quotient MulActionHom.toQuotient

@[simp]
theorem MulActionHom.to_quotient_apply (H : Subgroup α) (g : α) : MulActionHom.toQuotient H g = g :=
  rfl
#align mul_action_hom.to_quotient_apply MulActionHom.to_quotient_apply

@[to_additive]
instance mulLeftCosetsCompSubtypeVal (H I : Subgroup α) : MulAction I (α ⧸ H) :=
  MulAction.compHom (α ⧸ H) (Subgroup.subtype I)
#align mul_action.mul_left_cosets_comp_subtype_val MulAction.mulLeftCosetsCompSubtypeVal

variable (α) {β} [MulAction α β] (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive "The canonical map from the quotient of the stabilizer to the set. "]
def ofQuotientStabilizer (g : α ⧸ MulAction.stabilizer α x) : β :=
  (Quotient.liftOn' g (· • x)) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (left_rel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]
      
#align mul_action.of_quotient_stabilizer MulAction.ofQuotientStabilizer

@[simp, to_additive]
theorem of_quotient_stabilizer_mk (g : α) : ofQuotientStabilizer α x (QuotientGroup.mk g) = g • x :=
  rfl
#align mul_action.of_quotient_stabilizer_mk MulAction.of_quotient_stabilizer_mk

@[to_additive]
theorem of_quotient_stabilizer_mem_orbit (g) : ofQuotientStabilizer α x g ∈ orbit α x :=
  (Quotient.inductionOn' g) fun g => ⟨g, rfl⟩
#align mul_action.of_quotient_stabilizer_mem_orbit MulAction.of_quotient_stabilizer_mem_orbit

@[to_additive]
theorem of_quotient_stabilizer_smul (g : α) (g' : α ⧸ MulAction.stabilizer α x) :
    ofQuotientStabilizer α x (g • g') = g • ofQuotientStabilizer α x g' :=
  (Quotient.inductionOn' g') fun _ => mul_smul _ _ _
#align mul_action.of_quotient_stabilizer_smul MulAction.of_quotient_stabilizer_smul

@[to_additive]
theorem injective_of_quotient_stabilizer : Function.Injective (ofQuotientStabilizer α x) :=
  fun y₁ y₂ =>
  (Quotient.inductionOn₂' y₁ y₂) fun g₁ g₂ (H : g₁ • x = g₂ • x) =>
    Quotient.sound' <| by
      rw [left_rel_apply]
      show (g₁⁻¹ * g₂) • x = x
      rw [mul_smul, ← H, inv_smul_smul]
#align mul_action.injective_of_quotient_stabilizer MulAction.injective_of_quotient_stabilizer

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbitEquivQuotientStabilizer (b : β) : orbit α b ≃ α ⧸ stabilizer α b :=
  Equiv.symm <|
    Equiv.ofBijective
      (fun g => ⟨ofQuotientStabilizer α b g, of_quotient_stabilizer_mem_orbit α b g⟩)
      ⟨fun x y hxy => injective_of_quotient_stabilizer α b (by convert congr_arg Subtype.val hxy),
        fun ⟨b, ⟨g, hgb⟩⟩ => ⟨g, Subtype.eq hgb⟩⟩
#align mul_action.orbit_equiv_quotient_stabilizer MulAction.orbitEquivQuotientStabilizer

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbitProdStabilizerEquivGroup (b : β) : orbit α b × stabilizer α b ≃ α :=
  (Equiv.prodCongr (orbitEquivQuotientStabilizer α _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientTimesSubgroup.symm
#align mul_action.orbit_prod_stabilizer_equiv_group MulAction.orbitProdStabilizerEquivGroup

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α] [Fintype <| orbit α b]
    [Fintype <| stabilizer α b] :
    Fintype.card (orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α := by
  rw [← Fintype.card_prod, Fintype.card_congr (orbit_prod_stabilizer_equiv_group α b)]
#align
  mul_action.card_orbit_mul_card_stabilizer_eq_card_group MulAction.card_orbit_mul_card_stabilizer_eq_card_group

@[simp, to_additive]
theorem orbit_equiv_quotient_stabilizer_symm_apply (b : β) (a : α) :
    ((orbitEquivQuotientStabilizer α b).symm a : β) = a • b :=
  rfl
#align
  mul_action.orbit_equiv_quotient_stabilizer_symm_apply MulAction.orbit_equiv_quotient_stabilizer_symm_apply

@[simp, to_additive]
theorem stabilizer_quotient {G} [Group G] (H : Subgroup G) :
    MulAction.stabilizer G ((1 : G) : G ⧸ H) = H :=
  by
  ext
  simp [QuotientGroup.eq]
#align mul_action.stabilizer_quotient MulAction.stabilizer_quotient

variable (β)

-- mathport name: exprΩ
local notation "Ω" => Quotient <| orbitRel α β

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "**Class formula** : given `G` a group acting on `X` and `φ` a function mapping each orbit of `X`\nunder this action (that is, each element of the quotient of `X` by the relation `orbit_rel G X`) to\nan element in this orbit, this gives a (noncomputable) bijection between `X` and the disjoint union\nof `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want `φ` to be `quotient.out'`, so we\nprovide `mul_action.self_equiv_sigma_orbits_quotient_stabilizer` as a special case. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive
           "to_additive"
           []
           []
           (to_additiveRest
            []
            []
            [(str
              "\"**Class formula** : given `G` an additive group acting on `X` and `φ` a function\\nmapping each orbit of `X` under this action (that is, each element of the quotient of `X` by the\\nrelation `orbit_rel G X`) to an element in this orbit, this gives a (noncomputable) bijection\\nbetween `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want\\n`φ` to be `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits_quotient_stabilizer`\\nas a special case. \"")])))]
        "]")]
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `selfEquivSigmaOrbitsQuotientStabilizer' [])
      (Command.optDeclSig
       [(Term.implicitBinder
         "{"
         [`φ]
         [":" (Term.arrow (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω") "→" `β)]
         "}")
        (Term.explicitBinder "(" [`hφ] [":" (Term.app `LeftInverse [`Quotient.mk' `φ])] [] ")")]
       [(Term.typeSpec
         ":"
         (Logic.Equiv.Defs.«term_≃_»
          `β
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ω)]
             [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
           ","
           (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])])))))])
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          `β
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ω)]
             [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
           ","
           (Term.app `orbitRel.Quotient.orbit [`ω])))
         ":="
         (Term.app `selfEquivSigmaOrbits' [`α `β]))
        [(calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `ω)]
              [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
            ","
            (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])]))))
          ":="
          (Term.app
           `Equiv.sigmaCongrRight
           [(Term.fun
             "fun"
             (Term.basicFun
              [`ω]
              []
              "=>"
              («term_<|_»
               (Term.proj
                («term_<|_»
                 `Equiv.Set.ofEq
                 "<|"
                 (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ]))
                "."
                `trans)
               "<|"
               (Term.app `orbitEquivQuotientStabilizer [`α (Term.app `φ [`ω])]))))]))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        (Logic.Equiv.Defs.«term_≃_»
         `β
         " ≃ "
         («termΣ_,_»
          "Σ"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `ω)]
            [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
          ","
          (Term.app `orbitRel.Quotient.orbit [`ω])))
        ":="
        (Term.app `selfEquivSigmaOrbits' [`α `β]))
       [(calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ω)]
             [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
           ","
           (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])]))))
         ":="
         (Term.app
          `Equiv.sigmaCongrRight
          [(Term.fun
            "fun"
            (Term.basicFun
             [`ω]
             []
             "=>"
             («term_<|_»
              (Term.proj
               («term_<|_»
                `Equiv.Set.ofEq
                "<|"
                (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ]))
               "."
               `trans)
              "<|"
              (Term.app `orbitEquivQuotientStabilizer [`α (Term.app `φ [`ω])]))))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Equiv.sigmaCongrRight
       [(Term.fun
         "fun"
         (Term.basicFun
          [`ω]
          []
          "=>"
          («term_<|_»
           (Term.proj
            («term_<|_»
             `Equiv.Set.ofEq
             "<|"
             (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ]))
            "."
            `trans)
           "<|"
           (Term.app `orbitEquivQuotientStabilizer [`α (Term.app `φ [`ω])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`ω]
        []
        "=>"
        («term_<|_»
         (Term.proj
          («term_<|_»
           `Equiv.Set.ofEq
           "<|"
           (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ]))
          "."
          `trans)
         "<|"
         (Term.app `orbitEquivQuotientStabilizer [`α (Term.app `φ [`ω])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj
        («term_<|_»
         `Equiv.Set.ofEq
         "<|"
         (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ]))
        "."
        `trans)
       "<|"
       (Term.app `orbitEquivQuotientStabilizer [`α (Term.app `φ [`ω])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `orbitEquivQuotientStabilizer [`α (Term.app `φ [`ω])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`ω])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`ω]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `orbitEquivQuotientStabilizer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       («term_<|_»
        `Equiv.Set.ofEq
        "<|"
        (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ]))
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       `Equiv.Set.ofEq
       "<|"
       (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `orbitRel.Quotient.orbit_eq_orbit_out
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Equiv.Set.ofEq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      `Equiv.Set.ofEq
      "<|"
      (Term.app `orbitRel.Quotient.orbit_eq_orbit_out [(Term.hole "_") `hφ]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Equiv.sigmaCongrRight
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Logic.Equiv.Defs.«term_≃_»
       (Term.hole "_")
       " ≃ "
       («termΣ_,_»
        "Σ"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `ω)]
          [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
        ","
        (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («termΣ_,_»
       "Σ"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `ω)]
         [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
       ","
       (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `stabilizer [`α (Term.app `φ [`ω])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`ω])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`ω]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stabilizer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 34, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'MulAction.GroupTheory.GroupAction.Quotient.termΩ._@.GroupTheory.GroupAction.Quotient._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      **Class formula** : given `G` a group acting on `X` and `φ` a function mapping each orbit of `X`
      under this action (that is, each element of the quotient of `X` by the relation `orbit_rel G X`) to
      an element in this orbit, this gives a (noncomputable) bijection between `X` and the disjoint union
      of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want `φ` to be `quotient.out'`, so we
      provide `mul_action.self_equiv_sigma_orbits_quotient_stabilizer` as a special case. -/
    @[
      to_additive
        "**Class formula** : given `G` an additive group acting on `X` and `φ` a function\nmapping each orbit of `X` under this action (that is, each element of the quotient of `X` by the\nrelation `orbit_rel G X`) to an element in this orbit, this gives a (noncomputable) bijection\nbetween `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want\n`φ` to be `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits_quotient_stabilizer`\nas a special case. "
      ]
    noncomputable
  def
    selfEquivSigmaOrbitsQuotientStabilizer'
    { φ : Ω → β } ( hφ : LeftInverse Quotient.mk' φ ) : β ≃ Σ ω : Ω , α ⧸ stabilizer α φ ω
    :=
      calc
        β ≃ Σ ω : Ω , orbitRel.Quotient.orbit ω := selfEquivSigmaOrbits' α β
        _ ≃ Σ ω : Ω , α ⧸ stabilizer α φ ω
          :=
          Equiv.sigmaCongrRight
            fun
              ω
                =>
                Equiv.Set.ofEq <| orbitRel.Quotient.orbit_eq_orbit_out _ hφ . trans
                  <|
                  orbitEquivQuotientStabilizer α φ ω
#align
  mul_action.self_equiv_sigma_orbits_quotient_stabilizer' MulAction.selfEquivSigmaOrbitsQuotientStabilizer'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "**Class formula** for a finite group acting on a finite type. See\n`mul_action.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using\n`quotient.out'`. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive
           "to_additive"
           []
           []
           (to_additiveRest
            []
            []
            [(str
              "\"**Class formula** for a finite group acting on a finite type. See\\n`add_action.card_eq_sum_card_add_group_div_card_stabilizer` for a specialized version using\\n`quotient.out'`.\"")])))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `card_eq_sum_card_group_div_card_stabilizer' [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Fintype [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Fintype [`β]) "]")
        (Term.instBinder
         "["
         []
         (Term.app `Fintype [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")])
         "]")
        (Term.instBinder
         "["
         []
         (Term.forall
          "∀"
          [`b]
          [(Term.typeSpec ":" `β)]
          ","
          («term_<|_» `Fintype "<|" (Term.app `stabilizer [`α `b])))
         "]")
        (Term.implicitBinder
         "{"
         [`φ]
         [":" (Term.arrow (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω") "→" `β)]
         "}")
        (Term.explicitBinder "(" [`hφ] [":" (Term.app `LeftInverse [`Quotient.mk' `φ])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `Fintype.card [`β])
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `ω)
            [(group ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]))
          ", "
          («term_/_»
           (Term.app `Fintype.card [`α])
           "/"
           (Term.app `Fintype.card [(Term.app `stabilizer [`α (Term.app `φ [`ω])])]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticClassical_
            "classical"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.forall
                     "∀"
                     [`ω]
                     [(Term.typeSpec ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]
                     ","
                     («term_=_»
                      («term_/_»
                       (Term.app `Fintype.card [`α])
                       "/"
                       (Term.app
                        `Fintype.card
                        [(Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))
                      "="
                      (Term.app
                       `Fintype.card
                       [(Algebra.Quotient.«term_⧸_»
                         `α
                         " ⧸ "
                         (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.intro "intro" [`ω])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          []
                          (Term.app
                           `Fintype.card_congr
                           [(Term.app
                             (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
                             [`α
                              (Term.hole "_")
                              («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))])]))
                         ","
                         (Tactic.rwRule [] `Fintype.card_prod)
                         ","
                         (Tactic.rwRule [] `Nat.mul_div_cancel)]
                        "]")
                       [])
                      []
                      (Tactic.exact
                       "exact"
                       (Term.app
                        `fintype.card_pos_iff.mpr
                        [(Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.tacticInfer_instance "infer_instance")])))]))]))))))
               []
               (Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `this)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_sigma)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `Fintype.card_congr
                    [(Term.app `self_equiv_sigma_orbits_quotient_stabilizer' [`α `β `hφ])]))]
                 "]")
                [])])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticClassical_
           "classical"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   (Term.forall
                    "∀"
                    [`ω]
                    [(Term.typeSpec ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]
                    ","
                    («term_=_»
                     («term_/_»
                      (Term.app `Fintype.card [`α])
                      "/"
                      (Term.app
                       `Fintype.card
                       [(Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))
                     "="
                     (Term.app
                      `Fintype.card
                      [(Algebra.Quotient.«term_⧸_»
                        `α
                        " ⧸ "
                        (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))))]
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.intro "intro" [`ω])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         []
                         (Term.app
                          `Fintype.card_congr
                          [(Term.app
                            (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
                            [`α
                             (Term.hole "_")
                             («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))])]))
                        ","
                        (Tactic.rwRule [] `Fintype.card_prod)
                        ","
                        (Tactic.rwRule [] `Nat.mul_div_cancel)]
                       "]")
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `fintype.card_pos_iff.mpr
                       [(Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.tacticInfer_instance "infer_instance")])))]))]))))))
              []
              (Mathlib.Tactic.tacticSimp_rw__
               "simp_rw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_sigma)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app
                   `Fintype.card_congr
                   [(Term.app `self_equiv_sigma_orbits_quotient_stabilizer' [`α `β `hφ])]))]
                "]")
               [])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticClassical_
       "classical"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`ω]
                [(Term.typeSpec ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]
                ","
                («term_=_»
                 («term_/_»
                  (Term.app `Fintype.card [`α])
                  "/"
                  (Term.app
                   `Fintype.card
                   [(Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))
                 "="
                 (Term.app
                  `Fintype.card
                  [(Algebra.Quotient.«term_⧸_»
                    `α
                    " ⧸ "
                    (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`ω])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app
                      `Fintype.card_congr
                      [(Term.app
                        (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
                        [`α
                         (Term.hole "_")
                         («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))])]))
                    ","
                    (Tactic.rwRule [] `Fintype.card_prod)
                    ","
                    (Tactic.rwRule [] `Nat.mul_div_cancel)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `fintype.card_pos_iff.mpr
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.tacticInfer_instance "infer_instance")])))]))]))))))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `this)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_sigma)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `Fintype.card_congr
               [(Term.app `self_equiv_sigma_orbits_quotient_stabilizer' [`α `β `hφ])]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_sigma)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Fintype.card_congr
           [(Term.app `self_equiv_sigma_orbits_quotient_stabilizer' [`α `β `hφ])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Fintype.card_congr
       [(Term.app `self_equiv_sigma_orbits_quotient_stabilizer' [`α `β `hφ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `self_equiv_sigma_orbits_quotient_stabilizer' [`α `β `hφ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `self_equiv_sigma_orbits_quotient_stabilizer'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `self_equiv_sigma_orbits_quotient_stabilizer' [`α `β `hφ])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.card_sigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`ω]
            [(Term.typeSpec ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]
            ","
            («term_=_»
             («term_/_»
              (Term.app `Fintype.card [`α])
              "/"
              (Term.app
               `Fintype.card
               [(Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))
             "="
             (Term.app
              `Fintype.card
              [(Algebra.Quotient.«term_⧸_»
                `α
                " ⧸ "
                (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`ω])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  `Fintype.card_congr
                  [(Term.app
                    (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
                    [`α
                     (Term.hole "_")
                     («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))])]))
                ","
                (Tactic.rwRule [] `Fintype.card_prod)
                ","
                (Tactic.rwRule [] `Nat.mul_div_cancel)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `fintype.card_pos_iff.mpr
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.tacticInfer_instance "infer_instance")])))]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`ω])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `Fintype.card_congr
               [(Term.app
                 (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
                 [`α
                  (Term.hole "_")
                  («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))])]))
             ","
             (Tactic.rwRule [] `Fintype.card_prod)
             ","
             (Tactic.rwRule [] `Nat.mul_div_cancel)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `fintype.card_pos_iff.mpr
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `fintype.card_pos_iff.mpr
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `fintype.card_pos_iff.mpr
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fintype.card_pos_iff.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `Fintype.card_congr
           [(Term.app
             (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
             [`α
              (Term.hole "_")
              («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))])]))
         ","
         (Tactic.rwRule [] `Fintype.card_prod)
         ","
         (Tactic.rwRule [] `Nat.mul_div_cancel)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.mul_div_cancel
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.card_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Fintype.card_congr
       [(Term.app
         (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
         [`α (Term.hole "_") («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
       [`α (Term.hole "_") («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`ω])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `stabilizer [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stabilizer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subgroup.groupEquivQuotientTimesSubgroup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.explicit "@" `Subgroup.groupEquivQuotientTimesSubgroup)
      [`α
       (Term.hole "_")
       (Term.paren "(" («term_<|_» (Term.app `stabilizer [`α]) "<|" (Term.app `φ [`ω])) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`ω])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`ω]
       [(Term.typeSpec ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]
       ","
       («term_=_»
        («term_/_»
         (Term.app `Fintype.card [`α])
         "/"
         (Term.app
          `Fintype.card
          [(Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))
        "="
        (Term.app
         `Fintype.card
         [(Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])]))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_/_»
        (Term.app `Fintype.card [`α])
        "/"
        (Term.app
         `Fintype.card
         [(Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))
       "="
       (Term.app
        `Fintype.card
        [(Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Fintype.card
       [(Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.app `φ [`ω])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `stabilizer [`α (Term.app `φ [`ω])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`ω])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`ω]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stabilizer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 34, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Quotient.«term_⧸_»
      `α
      " ⧸ "
      (Term.app `stabilizer [`α (Term.paren "(" (Term.app `φ [`ω]) ")")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_/_»
       (Term.app `Fintype.card [`α])
       "/"
       (Term.app
        `Fintype.card
        [(Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Fintype.card
       [(Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Coe.«term↥_» "↥" (Term.app `stabilizer [`α (Term.app `φ [`ω])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `stabilizer [`α (Term.app `φ [`ω])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`ω])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`ω]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stabilizer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `stabilizer [`α (Term.paren "(" (Term.app `φ [`ω]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1023, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `Fintype.card [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'MulAction.GroupTheory.GroupAction.Quotient.termΩ._@.GroupTheory.GroupAction.Quotient._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      **Class formula** for a finite group acting on a finite type. See
      `mul_action.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using
      `quotient.out'`. -/
    @[
      to_additive
        "**Class formula** for a finite group acting on a finite type. See\n`add_action.card_eq_sum_card_add_group_div_card_stabilizer` for a specialized version using\n`quotient.out'`."
      ]
  theorem
    card_eq_sum_card_group_div_card_stabilizer'
    [ Fintype α ]
        [ Fintype β ]
        [ Fintype Ω ]
        [ ∀ b : β , Fintype <| stabilizer α b ]
        { φ : Ω → β }
        ( hφ : LeftInverse Quotient.mk' φ )
      : Fintype.card β = ∑ ω : Ω , Fintype.card α / Fintype.card stabilizer α φ ω
    :=
      by
        classical
          have
              :
                  ∀
                    ω
                    : Ω
                    ,
                    Fintype.card α / Fintype.card ↥ stabilizer α φ ω
                      =
                      Fintype.card α ⧸ stabilizer α φ ω
                :=
                by
                  intro ω
                    rw
                      [
                        Fintype.card_congr
                            @ Subgroup.groupEquivQuotientTimesSubgroup α _ stabilizer α <| φ ω
                          ,
                          Fintype.card_prod
                          ,
                          Nat.mul_div_cancel
                        ]
                    exact fintype.card_pos_iff.mpr by infer_instance
            simp_rw
              [
                this
                  ,
                  ← Fintype.card_sigma
                  ,
                  Fintype.card_congr self_equiv_sigma_orbits_quotient_stabilizer' α β hφ
                ]
#align
  mul_action.card_eq_sum_card_group_div_card_stabilizer' MulAction.card_eq_sum_card_group_div_card_stabilizer'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "**Class formula**. This is a special case of\n`mul_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive
           "to_additive"
           []
           []
           (to_additiveRest
            []
            []
            [(str
              "\"**Class formula**. This is a special case of\\n`add_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. \"")])))]
        "]")]
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `selfEquivSigmaOrbitsQuotientStabilizer [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Logic.Equiv.Defs.«term_≃_»
          `β
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ω)]
             [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
           ","
           (Algebra.Quotient.«term_⧸_»
            `α
            " ⧸ "
            (Term.app `stabilizer [`α (Term.proj `ω "." `out')])))))])
      (Command.declValSimple
       ":="
       (Term.app `selfEquivSigmaOrbitsQuotientStabilizer' [`α `β `Quotient.out_eq'])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `selfEquivSigmaOrbitsQuotientStabilizer' [`α `β `Quotient.out_eq'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Quotient.out_eq'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `selfEquivSigmaOrbitsQuotientStabilizer'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Logic.Equiv.Defs.«term_≃_»
       `β
       " ≃ "
       («termΣ_,_»
        "Σ"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `ω)]
          [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
        ","
        (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.proj `ω "." `out')]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («termΣ_,_»
       "Σ"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `ω)]
         [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
       ","
       (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.proj `ω "." `out')])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_» `α " ⧸ " (Term.app `stabilizer [`α (Term.proj `ω "." `out')]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `stabilizer [`α (Term.proj `ω "." `out')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `ω "." `out')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stabilizer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 34, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'MulAction.GroupTheory.GroupAction.Quotient.termΩ._@.GroupTheory.GroupAction.Quotient._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      **Class formula**. This is a special case of
      `mul_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. -/
    @[
      to_additive
        "**Class formula**. This is a special case of\n`add_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. "
      ]
    noncomputable
  def
    selfEquivSigmaOrbitsQuotientStabilizer
    : β ≃ Σ ω : Ω , α ⧸ stabilizer α ω . out'
    := selfEquivSigmaOrbitsQuotientStabilizer' α β Quotient.out_eq'
#align
  mul_action.self_equiv_sigma_orbits_quotient_stabilizer MulAction.selfEquivSigmaOrbitsQuotientStabilizer

/- failed to parenthesize: unknown constant 'group'
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "**Class formula** for a finite group acting on a finite type. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive
           "to_additive"
           []
           []
           (to_additiveRest
            []
            []
            [(str "\"**Class formula** for a finite group acting on a finite type.\"")])))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `card_eq_sum_card_group_div_card_stabilizer [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Fintype [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Fintype [`β]) "]")
        (Term.instBinder
         "["
         []
         (Term.app `Fintype [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")])
         "]")
        (Term.instBinder
         "["
         []
         (Term.forall
          "∀"
          [`b]
          [(Term.typeSpec ":" `β)]
          ","
          («term_<|_» `Fintype "<|" (Term.app `stabilizer [`α `b])))
         "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `Fintype.card [`β])
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `ω)
            [(group ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]))
          ", "
          («term_/_»
           (Term.app `Fintype.card [`α])
           "/"
           (Term.app `Fintype.card [(Term.app `stabilizer [`α (Term.proj `ω "." `out')])]))))))
      (Command.declValSimple
       ":="
       (Term.app `card_eq_sum_card_group_div_card_stabilizer' [`α `β `Quotient.out_eq'])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `card_eq_sum_card_group_div_card_stabilizer' [`α `β `Quotient.out_eq'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Quotient.out_eq'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `card_eq_sum_card_group_div_card_stabilizer'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `Fintype.card [`β])
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `ω)
          [(group ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]))
        ", "
        («term_/_»
         (Term.app `Fintype.card [`α])
         "/"
         (Term.app `Fintype.card [(Term.app `stabilizer [`α (Term.proj `ω "." `out')])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `ω)
         [(group ":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω"))]))
       ", "
       («term_/_»
        (Term.app `Fintype.card [`α])
        "/"
        (Term.app `Fintype.card [(Term.app `stabilizer [`α (Term.proj `ω "." `out')])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       (Term.app `Fintype.card [`α])
       "/"
       (Term.app `Fintype.card [(Term.app `stabilizer [`α (Term.proj `ω "." `out')])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fintype.card [(Term.app `stabilizer [`α (Term.proj `ω "." `out')])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `stabilizer [`α (Term.proj `ω "." `out')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `ω "." `out')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ω
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `stabilizer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `stabilizer [`α (Term.proj `ω "." `out')])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `Fintype.card [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'MulAction.GroupTheory.GroupAction.Quotient.termΩ._@.GroupTheory.GroupAction.Quotient._hyg.11'-/-- failed to format: unknown constant 'group'
/-- **Class formula** for a finite group acting on a finite type. -/
    @[ to_additive "**Class formula** for a finite group acting on a finite type." ]
  theorem
    card_eq_sum_card_group_div_card_stabilizer
    [ Fintype α ] [ Fintype β ] [ Fintype Ω ] [ ∀ b : β , Fintype <| stabilizer α b ]
      : Fintype.card β = ∑ ω : Ω , Fintype.card α / Fintype.card stabilizer α ω . out'
    := card_eq_sum_card_group_div_card_stabilizer' α β Quotient.out_eq'
#align
  mul_action.card_eq_sum_card_group_div_card_stabilizer MulAction.card_eq_sum_card_group_div_card_stabilizer

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "**Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all\n`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is a group acting on `X` and\n`X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive
           "to_additive"
           []
           []
           (to_additiveRest
            []
            []
            [(str
              "\"**Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all\\n`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is an additive group acting\\non `X` and `X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. \"")])))]
        "]")]
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `sigmaFixedByEquivOrbitsProdGroup [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Logic.Equiv.Defs.«term_≃_»
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
           ","
           (Term.app `fixedBy [`α `β `a]))
          " ≃ "
          («term_×_» (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω") "×" `α)))])
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
           ","
           (Term.app `fixedBy [`α `β `a]))
          " ≃ "
          («term{_:_//_}»
           "{"
           `ab
           [":" («term_×_» `α "×" `β)]
           "//"
           («term_=_»
            (Algebra.Group.Defs.«term_•_»
             (Term.proj `ab "." (fieldIdx "1"))
             " • "
             (Term.proj `ab "." (fieldIdx "2")))
            "="
            (Term.proj `ab "." (fieldIdx "2")))
           "}"))
         ":="
         (Term.proj (Term.app `Equiv.subtypeProdEquivSigmaSubtype [(Term.hole "_")]) "." `symm))
        [(calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («term{_:_//_}»
            "{"
            `ba
            [":" («term_×_» `β "×" `α)]
            "//"
            («term_=_»
             (Algebra.Group.Defs.«term_•_»
              (Term.proj `ba "." (fieldIdx "2"))
              " • "
              (Term.proj `ba "." (fieldIdx "1")))
             "="
             (Term.proj `ba "." (fieldIdx "1")))
            "}"))
          ":="
          (Term.app
           (Term.proj (Term.app `Equiv.prodComm [`α `β]) "." `subtypeEquiv)
           [(Term.fun "fun" (Term.basicFun [`ab] [] "=>" `Iff.rfl))]))
         (calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" `β]))
            ","
            (Term.app `stabilizer [`α `b])))
          ":="
          (Term.app
           `Equiv.subtypeProdEquivSigmaSubtype
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.typeAscription "(" (Term.app `b []) ":" [`β] ")") `a]
              []
              "=>"
              («term_∈_» `a "∈" (Term.app `stabilizer [`α `b]))))]))
         (calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `ωb)]
              [":"
               («termΣ_,_»
                "Σ"
                (Lean.explicitBinders
                 (Lean.unbracketedExplicitBinders
                  [(Lean.binderIdent `ω)]
                  [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
                ","
                (Term.app `orbit [`α (Term.proj `ω "." `out')]))]))
            ","
            (Term.app
             `stabilizer
             [`α (Term.typeAscription "(" (Term.proj `ωb "." (fieldIdx "2")) ":" [`β] ")")])))
          ":="
          (Term.proj (Term.app `selfEquivSigmaOrbits [`α `β]) "." `sigmaCongrLeft'))
         (calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `ω)]
              [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
            ","
            («termΣ_,_»
             "Σ"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `b)]
               [":" (Term.app `orbit [`α (Term.proj `ω "." `out')])]))
             ","
             (Term.app `stabilizer [`α (Term.typeAscription "(" `b ":" [`β] ")")]))))
          ":="
          (Term.app
           `Equiv.sigmaAssoc
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.typeAscription
                "("
                (Term.app `ω [])
                ":"
                [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]
                ")")
               (Term.typeAscription
                "("
                (Term.app `b [])
                ":"
                [(Term.app `orbit [`α (Term.proj `ω "." `out')])]
                ")")]
              []
              "=>"
              (Term.app `stabilizer [`α (Term.typeAscription "(" `b ":" [`β] ")")])))]))
         (calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `ω)]
              [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
            ","
            («termΣ_,_»
             "Σ"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `b)]
               [":" (Term.app `orbit [`α (Term.proj `ω "." `out')])]))
             ","
             (Term.app `stabilizer [`α (Term.proj `ω "." `out')]))))
          ":="
          (Term.app
           `Equiv.sigmaCongrRight
           [(Term.fun
             "fun"
             (Term.basicFun
              [`ω]
              []
              "=>"
              (Term.app
               `Equiv.sigmaCongrRight
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.anonymousCtor "⟨" [`b "," `hb] "⟩")]
                  []
                  "=>"
                  (Term.proj
                   (Term.app `stabilizerEquivStabilizerOfOrbitRel [`hb])
                   "."
                   `toEquiv)))])))]))
         (calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `ω)]
              [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
            ","
            («term_×_»
             (Term.app `orbit [`α (Term.proj `ω "." `out')])
             "×"
             (Term.app `stabilizer [`α (Term.proj `ω "." `out')]))))
          ":="
          (Term.app
           `Equiv.sigmaCongrRight
           [(Term.fun
             "fun"
             (Term.basicFun
              [`ω]
              []
              "=>"
              (Term.app `Equiv.sigmaEquivProd [(Term.hole "_") (Term.hole "_")])))]))
         (calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `ω)]
              [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
            ","
            `α))
          ":="
          (Term.app
           `Equiv.sigmaCongrRight
           [(Term.fun
             "fun"
             (Term.basicFun
              [`ω]
              []
              "=>"
              (Term.app `orbitProdStabilizerEquivGroup [`α (Term.proj `ω "." `out')])))]))
         (calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («term_×_» (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω") "×" `α))
          ":="
          (Term.app
           `Equiv.sigmaEquivProd
           [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω") `α]))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        (Logic.Equiv.Defs.«term_≃_»
         («termΣ_,_»
          "Σ"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] [":" `α]))
          ","
          (Term.app `fixedBy [`α `β `a]))
         " ≃ "
         («term{_:_//_}»
          "{"
          `ab
          [":" («term_×_» `α "×" `β)]
          "//"
          («term_=_»
           (Algebra.Group.Defs.«term_•_»
            (Term.proj `ab "." (fieldIdx "1"))
            " • "
            (Term.proj `ab "." (fieldIdx "2")))
           "="
           (Term.proj `ab "." (fieldIdx "2")))
          "}"))
        ":="
        (Term.proj (Term.app `Equiv.subtypeProdEquivSigmaSubtype [(Term.hole "_")]) "." `symm))
       [(calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («term{_:_//_}»
           "{"
           `ba
           [":" («term_×_» `β "×" `α)]
           "//"
           («term_=_»
            (Algebra.Group.Defs.«term_•_»
             (Term.proj `ba "." (fieldIdx "2"))
             " • "
             (Term.proj `ba "." (fieldIdx "1")))
            "="
            (Term.proj `ba "." (fieldIdx "1")))
           "}"))
         ":="
         (Term.app
          (Term.proj (Term.app `Equiv.prodComm [`α `β]) "." `subtypeEquiv)
          [(Term.fun "fun" (Term.basicFun [`ab] [] "=>" `Iff.rfl))]))
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `b)] [":" `β]))
           ","
           (Term.app `stabilizer [`α `b])))
         ":="
         (Term.app
          `Equiv.subtypeProdEquivSigmaSubtype
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.typeAscription "(" (Term.app `b []) ":" [`β] ")") `a]
             []
             "=>"
             («term_∈_» `a "∈" (Term.app `stabilizer [`α `b]))))]))
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ωb)]
             [":"
              («termΣ_,_»
               "Σ"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders
                 [(Lean.binderIdent `ω)]
                 [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
               ","
               (Term.app `orbit [`α (Term.proj `ω "." `out')]))]))
           ","
           (Term.app
            `stabilizer
            [`α (Term.typeAscription "(" (Term.proj `ωb "." (fieldIdx "2")) ":" [`β] ")")])))
         ":="
         (Term.proj (Term.app `selfEquivSigmaOrbits [`α `β]) "." `sigmaCongrLeft'))
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ω)]
             [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
           ","
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `b)]
              [":" (Term.app `orbit [`α (Term.proj `ω "." `out')])]))
            ","
            (Term.app `stabilizer [`α (Term.typeAscription "(" `b ":" [`β] ")")]))))
         ":="
         (Term.app
          `Equiv.sigmaAssoc
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.typeAscription
               "("
               (Term.app `ω [])
               ":"
               [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]
               ")")
              (Term.typeAscription
               "("
               (Term.app `b [])
               ":"
               [(Term.app `orbit [`α (Term.proj `ω "." `out')])]
               ")")]
             []
             "=>"
             (Term.app `stabilizer [`α (Term.typeAscription "(" `b ":" [`β] ")")])))]))
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ω)]
             [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
           ","
           («termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `b)]
              [":" (Term.app `orbit [`α (Term.proj `ω "." `out')])]))
            ","
            (Term.app `stabilizer [`α (Term.proj `ω "." `out')]))))
         ":="
         (Term.app
          `Equiv.sigmaCongrRight
          [(Term.fun
            "fun"
            (Term.basicFun
             [`ω]
             []
             "=>"
             (Term.app
              `Equiv.sigmaCongrRight
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`b "," `hb] "⟩")]
                 []
                 "=>"
                 (Term.proj
                  (Term.app `stabilizerEquivStabilizerOfOrbitRel [`hb])
                  "."
                  `toEquiv)))])))]))
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ω)]
             [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
           ","
           («term_×_»
            (Term.app `orbit [`α (Term.proj `ω "." `out')])
            "×"
            (Term.app `stabilizer [`α (Term.proj `ω "." `out')]))))
         ":="
         (Term.app
          `Equiv.sigmaCongrRight
          [(Term.fun
            "fun"
            (Term.basicFun
             [`ω]
             []
             "=>"
             (Term.app `Equiv.sigmaEquivProd [(Term.hole "_") (Term.hole "_")])))]))
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ω)]
             [":" (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")]))
           ","
           `α))
         ":="
         (Term.app
          `Equiv.sigmaCongrRight
          [(Term.fun
            "fun"
            (Term.basicFun
             [`ω]
             []
             "=>"
             (Term.app `orbitProdStabilizerEquivGroup [`α (Term.proj `ω "." `out')])))]))
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («term_×_» (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω") "×" `α))
         ":="
         (Term.app
          `Equiv.sigmaEquivProd
          [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω") `α]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Equiv.sigmaEquivProd [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω") `α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'MulAction.GroupTheory.GroupAction.Quotient.termΩ._@.GroupTheory.GroupAction.Quotient._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
      `{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is a group acting on `X` and
      `X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. -/
    @[
      to_additive
        "**Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all\n`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is an additive group acting\non `X` and `X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. "
      ]
    noncomputable
  def
    sigmaFixedByEquivOrbitsProdGroup
    : Σ a : α , fixedBy α β a ≃ Ω × α
    :=
      calc
        Σ a : α , fixedBy α β a ≃ { ab : α × β // ab . 1 • ab . 2 = ab . 2 }
          :=
          Equiv.subtypeProdEquivSigmaSubtype _ . symm
        _ ≃ { ba : β × α // ba . 2 • ba . 1 = ba . 1 }
            :=
            Equiv.prodComm α β . subtypeEquiv fun ab => Iff.rfl
          _ ≃ Σ b : β , stabilizer α b
            :=
            Equiv.subtypeProdEquivSigmaSubtype fun ( b : β ) a => a ∈ stabilizer α b
          _ ≃ Σ ωb : Σ ω : Ω , orbit α ω . out' , stabilizer α ( ωb . 2 : β )
            :=
            selfEquivSigmaOrbits α β . sigmaCongrLeft'
          _ ≃ Σ ω : Ω , Σ b : orbit α ω . out' , stabilizer α ( b : β )
            :=
            Equiv.sigmaAssoc fun ( ω : Ω ) ( b : orbit α ω . out' ) => stabilizer α ( b : β )
          _ ≃ Σ ω : Ω , Σ b : orbit α ω . out' , stabilizer α ω . out'
            :=
            Equiv.sigmaCongrRight
              fun
                ω
                  =>
                  Equiv.sigmaCongrRight
                    fun ⟨ b , hb ⟩ => stabilizerEquivStabilizerOfOrbitRel hb . toEquiv
          _ ≃ Σ ω : Ω , orbit α ω . out' × stabilizer α ω . out'
            :=
            Equiv.sigmaCongrRight fun ω => Equiv.sigmaEquivProd _ _
          _ ≃ Σ ω : Ω , α := Equiv.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup α ω . out'
          _ ≃ Ω × α := Equiv.sigmaEquivProd Ω α
#align mul_action.sigma_fixed_by_equiv_orbits_prod_group MulAction.sigmaFixedByEquivOrbitsProdGroup

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "**Burnside's lemma** : given a finite group `G` acting on a set `X`, the average number of\nelements fixed by each `g ∈ G` is the number of orbits. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive
           "to_additive"
           []
           []
           (to_additiveRest
            []
            []
            [(str
              "\"**Burnside's lemma** : given a finite additive group `G` acting on a set `X`,\\nthe average number of elements fixed by each `g ∈ G` is the number of orbits. \"")])))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `sum_card_fixed_by_eq_card_orbits_mul_card_group [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Fintype [`α]) "]")
        (Term.instBinder
         "["
         []
         (Term.forall "∀" [`a] [] "," («term_<|_» `Fintype "<|" (Term.app `fixedBy [`α `β `a])))
         "]")
        (Term.instBinder
         "["
         []
         (Term.app `Fintype [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")])
         "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `α)]))
          ", "
          (Term.app `Fintype.card [(Term.app `fixedBy [`α `β `a])]))
         "="
         («term_*_»
          (Term.app `Fintype.card [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")])
          "*"
          (Term.app `Fintype.card [`α])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_prod)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_sigma)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `Fintype.card_congr
                [(Term.app `sigma_fixed_by_equiv_orbits_prod_group [`α `β])]))]
             "]")
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_prod)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_sigma)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `Fintype.card_congr
               [(Term.app `sigma_fixed_by_equiv_orbits_prod_group [`α `β])]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_prod)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Fintype.card_sigma)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Fintype.card_congr
           [(Term.app `sigma_fixed_by_equiv_orbits_prod_group [`α `β])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fintype.card_congr [(Term.app `sigma_fixed_by_equiv_orbits_prod_group [`α `β])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sigma_fixed_by_equiv_orbits_prod_group [`α `β])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `β
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sigma_fixed_by_equiv_orbits_prod_group
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sigma_fixed_by_equiv_orbits_prod_group [`α `β])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.card_sigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.card_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `a) [(group ":" `α)]))
        ", "
        (Term.app `Fintype.card [(Term.app `fixedBy [`α `β `a])]))
       "="
       («term_*_»
        (Term.app `Fintype.card [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")])
        "*"
        (Term.app `Fintype.card [`α])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `Fintype.card [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")])
       "*"
       (Term.app `Fintype.card [`α]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fintype.card [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.card
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `Fintype.card [(MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (MulAction.GroupTheory.GroupAction.Quotient.termΩ "Ω")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'MulAction.GroupTheory.GroupAction.Quotient.termΩ', expected 'MulAction.GroupTheory.GroupAction.Quotient.termΩ._@.GroupTheory.GroupAction.Quotient._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      **Burnside's lemma** : given a finite group `G` acting on a set `X`, the average number of
      elements fixed by each `g ∈ G` is the number of orbits. -/
    @[
      to_additive
        "**Burnside's lemma** : given a finite additive group `G` acting on a set `X`,\nthe average number of elements fixed by each `g ∈ G` is the number of orbits. "
      ]
  theorem
    sum_card_fixed_by_eq_card_orbits_mul_card_group
    [ Fintype α ] [ ∀ a , Fintype <| fixedBy α β a ] [ Fintype Ω ]
      : ∑ a : α , Fintype.card fixedBy α β a = Fintype.card Ω * Fintype.card α
    :=
      by
        rw
          [
            ← Fintype.card_prod
              ,
              ← Fintype.card_sigma
              ,
              Fintype.card_congr sigma_fixed_by_equiv_orbits_prod_group α β
            ]
#align
  mul_action.sum_card_fixed_by_eq_card_orbits_mul_card_group MulAction.sum_card_fixed_by_eq_card_orbits_mul_card_group

@[to_additive]
instance is_pretransitive_quotient (G) [Group G] (H : Subgroup G) : IsPretransitive G (G ⧸ H)
    where exists_smul_eq := by
    rintro ⟨x⟩ ⟨y⟩
    refine' ⟨y * x⁻¹, quotient_group.eq.mpr _⟩
    simp only [smul_eq_mul, H.one_mem, mul_left_inv, inv_mul_cancel_right]
#align mul_action.is_pretransitive_quotient MulAction.is_pretransitive_quotient

end MulAction

namespace Subgroup

variable {G : Type _} [Group G] (H : Subgroup G)

theorem normal_core_eq_ker : H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker :=
  by
  refine'
    le_antisymm
      (fun g hg =>
        Equiv.Perm.ext fun q =>
          QuotientGroup.induction_on q fun g' =>
            (MulAction.quotient.smul_mk H g g').trans (quotient_group.eq.mpr _))
      (subgroup.normal_le_normal_core.mpr fun g hg => _)
  · rw [smul_eq_mul, mul_inv_rev, ← inv_inv g', inv_inv]
    exact H.normal_core.inv_mem hg g'⁻¹
  · rw [← H.inv_mem_iff, ← mul_one g⁻¹, ← QuotientGroup.eq, ← mul_one g]
    exact (MulAction.quotient.smul_mk H g 1).symm.trans (equiv.perm.ext_iff.mp hg (1 : G))
#align subgroup.normal_core_eq_ker Subgroup.normal_core_eq_ker

open QuotientGroup

/-- Cosets of the centralizer of an element embed into the set of commutators. -/
noncomputable def quotientCentralizerEmbedding (g : G) :
    G ⧸ centralizer (zpowers (g : G)) ↪ commutatorSet G :=
  ((MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).trans
            (quotientEquivOfEq (ConjAct.stabilizer_eq_centralizer g))).symm.toEmbedding.trans
    ⟨fun x =>
      ⟨x * g⁻¹,
        let ⟨_, x, rfl⟩ := x
        ⟨x, g, rfl⟩⟩,
      fun x y => Subtype.ext ∘ mul_right_cancel ∘ Subtype.ext_iff.mp⟩
#align subgroup.quotient_centralizer_embedding Subgroup.quotientCentralizerEmbedding

theorem quotient_centralizer_embedding_apply (g : G) (x : G) :
    quotientCentralizerEmbedding g x = ⟨⁅x, g⁆, x, g, rfl⟩ :=
  rfl
#align subgroup.quotient_centralizer_embedding_apply Subgroup.quotient_centralizer_embedding_apply

/-- If `G` is generated by `S`, then the quotient by the center embeds into `S`-indexed sequences
of commutators. -/
noncomputable def quotientCenterEmbedding {S : Set G} (hS : closure S = ⊤) :
    G ⧸ center G ↪ S → commutatorSet G :=
  (quotientEquivOfEq (center_eq_infi' S hS)).toEmbedding.trans
    ((quotientInfiEmbedding _).trans
      (Function.Embedding.piCongrRight fun g => quotientCentralizerEmbedding g))
#align subgroup.quotient_center_embedding Subgroup.quotientCenterEmbedding

theorem quotient_center_embedding_apply {S : Set G} (hS : closure S = ⊤) (g : G) (s : S) :
    quotientCenterEmbedding hS g s = ⟨⁅g, s⁆, g, s, rfl⟩ :=
  rfl
#align subgroup.quotient_center_embedding_apply Subgroup.quotient_center_embedding_apply

end Subgroup

