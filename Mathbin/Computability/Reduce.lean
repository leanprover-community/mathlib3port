/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro

! This file was ported from Lean 3 source module computability.reduce
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Computability.Halting

/-!
# Strong reducibility and degrees.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notations

This file uses the local notation `⊕'` for `sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/


universe u v w

open Function

/--
`p` is many-one reducible to `q` if there is a computable function translating questions about `p`
to questions about `q`.
-/
def ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ ∀ a, p a ↔ q (f a)
#align many_one_reducible ManyOneReducible

-- mathport name: «expr ≤₀ »
infixl:1000 " ≤₀ " => ManyOneReducible

theorem ManyOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) : (fun a => q (f a)) ≤₀ q :=
  ⟨f, h, fun a => Iff.rfl⟩
#align many_one_reducible.mk ManyOneReducible.mk

@[refl]
theorem many_one_reducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₀ p :=
  ⟨id, Computable.id, by simp⟩
#align many_one_reducible_refl many_one_reducible_refl

@[trans]
theorem ManyOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ q → q ≤₀ r → p ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, fun a => ⟨fun h => by rwa [← h₂, ← h₁], fun h => by rwa [h₁, h₂]⟩⟩
#align many_one_reducible.trans ManyOneReducible.trans

theorem reflexive_many_one_reducible {α} [Primcodable α] : Reflexive (@ManyOneReducible α α _ _) :=
  many_one_reducible_refl
#align reflexive_many_one_reducible reflexive_many_one_reducible

theorem transitive_many_one_reducible {α} [Primcodable α] :
    Transitive (@ManyOneReducible α α _ _) := fun p q r => ManyOneReducible.trans
#align transitive_many_one_reducible transitive_many_one_reducible

/--
`p` is one-one reducible to `q` if there is an injective computable function translating questions
about `p` to questions about `q`.
-/
def OneOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ Injective f ∧ ∀ a, p a ↔ q (f a)
#align one_one_reducible OneOneReducible

-- mathport name: «expr ≤₁ »
infixl:1000 " ≤₁ " => OneOneReducible

theorem OneOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop)
    (h : Computable f) (i : Injective f) : (fun a => q (f a)) ≤₁ q :=
  ⟨f, h, i, fun a => Iff.rfl⟩
#align one_one_reducible.mk OneOneReducible.mk

@[refl]
theorem one_one_reducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₁ p :=
  ⟨id, Computable.id, injective_id, by simp⟩
#align one_one_reducible_refl one_one_reducible_refl

@[trans]
theorem OneOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : p ≤₁ q → q ≤₁ r → p ≤₁ r
  | ⟨f, c₁, i₁, h₁⟩, ⟨g, c₂, i₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, i₂.comp i₁, fun a =>
      ⟨fun h => by rwa [← h₂, ← h₁], fun h => by rwa [h₁, h₂]⟩⟩
#align one_one_reducible.trans OneOneReducible.trans

theorem OneOneReducible.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : p ≤₁ q → p ≤₀ q
  | ⟨f, c, i, h⟩ => ⟨f, c, h⟩
#align one_one_reducible.to_many_one OneOneReducible.to_many_one

theorem OneOneReducible.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β → Prop)
    (h : Computable e) : (q ∘ e) ≤₁ q :=
  OneOneReducible.mk _ h e.Injective
#align one_one_reducible.of_equiv OneOneReducible.of_equiv

theorem OneOneReducible.of_equiv_symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
    (q : β → Prop) (h : Computable e.symm) : q ≤₁ (q ∘ e) := by
  convert OneOneReducible.of_equiv _ h <;> funext <;> simp
#align one_one_reducible.of_equiv_symm OneOneReducible.of_equiv_symm

theorem reflexive_one_one_reducible {α} [Primcodable α] : Reflexive (@OneOneReducible α α _ _) :=
  one_one_reducible_refl
#align reflexive_one_one_reducible reflexive_one_one_reducible

theorem transitive_one_one_reducible {α} [Primcodable α] : Transitive (@OneOneReducible α α _ _) :=
  fun p q r => OneOneReducible.trans
#align transitive_one_one_reducible transitive_one_one_reducible

namespace ComputablePred

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Computable

theorem computable_of_many_one_reducible {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q)
    (h₂ : ComputablePred q) : ComputablePred p :=
  by
  rcases h₁ with ⟨f, c, hf⟩
  rw [show p = fun a => q (f a) from Set.ext hf]
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩
  exact ⟨by infer_instance, by simpa using hg.comp c⟩
#align
  computable_pred.computable_of_many_one_reducible ComputablePred.computable_of_many_one_reducible

theorem computable_of_one_one_reducible {p : α → Prop} {q : β → Prop} (h : p ≤₁ q) :
    ComputablePred q → ComputablePred p :=
  computable_of_many_one_reducible h.to_many_one
#align
  computable_pred.computable_of_one_one_reducible ComputablePred.computable_of_one_one_reducible

end ComputablePred

/-- `p` and `q` are many-one equivalent if each one is many-one reducible to the other. -/
def ManyOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₀ q ∧ q ≤₀ p
#align many_one_equiv ManyOneEquiv

/-- `p` and `q` are one-one equivalent if each one is one-one reducible to the other. -/
def OneOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₁ q ∧ q ≤₁ p
#align one_one_equiv OneOneEquiv

@[refl]
theorem many_one_equiv_refl {α} [Primcodable α] (p : α → Prop) : ManyOneEquiv p p :=
  ⟨many_one_reducible_refl _, many_one_reducible_refl _⟩
#align many_one_equiv_refl many_one_equiv_refl

@[symm]
theorem ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    ManyOneEquiv p q → ManyOneEquiv q p :=
  And.symm
#align many_one_equiv.symm ManyOneEquiv.symm

@[trans]
theorem ManyOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : ManyOneEquiv p q → ManyOneEquiv q r → ManyOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩
#align many_one_equiv.trans ManyOneEquiv.trans

theorem equivalence_of_many_one_equiv {α} [Primcodable α] : Equivalence (@ManyOneEquiv α α _ _) :=
  ⟨many_one_equiv_refl, fun x y => ManyOneEquiv.symm, fun x y z => ManyOneEquiv.trans⟩
#align equivalence_of_many_one_equiv equivalence_of_many_one_equiv

@[refl]
theorem one_one_equiv_refl {α} [Primcodable α] (p : α → Prop) : OneOneEquiv p p :=
  ⟨one_one_reducible_refl _, one_one_reducible_refl _⟩
#align one_one_equiv_refl one_one_equiv_refl

@[symm]
theorem OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    OneOneEquiv p q → OneOneEquiv q p :=
  And.symm
#align one_one_equiv.symm OneOneEquiv.symm

@[trans]
theorem OneOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} : OneOneEquiv p q → OneOneEquiv q r → OneOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩
#align one_one_equiv.trans OneOneEquiv.trans

theorem equivalence_of_one_one_equiv {α} [Primcodable α] : Equivalence (@OneOneEquiv α α _ _) :=
  ⟨one_one_equiv_refl, fun x y => OneOneEquiv.symm, fun x y z => OneOneEquiv.trans⟩
#align equivalence_of_one_one_equiv equivalence_of_one_one_equiv

theorem OneOneEquiv.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} : OneOneEquiv p q → ManyOneEquiv p q
  | ⟨pq, qp⟩ => ⟨pq.to_many_one, qp.to_many_one⟩
#align one_one_equiv.to_many_one OneOneEquiv.to_many_one

/-- a computable bijection -/
def Equiv.Computable {α β} [Primcodable α] [Primcodable β] (e : α ≃ β) :=
  Computable e ∧ Computable e.symm
#align equiv.computable Equiv.Computable

theorem Equiv.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} :
    e.Computable → e.symm.Computable :=
  And.symm
#align equiv.computable.symm Equiv.Computable.symm

theorem Equiv.Computable.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}
    {e₂ : β ≃ γ} : e₁.Computable → e₂.Computable → (e₁.trans e₂).Computable
  | ⟨l₁, r₁⟩, ⟨l₂, r₂⟩ => ⟨l₂.comp l₁, r₁.comp r₂⟩
#align equiv.computable.trans Equiv.Computable.trans

theorem Computable.eqv (α) [Denumerable α] : (Denumerable.eqv α).Computable :=
  ⟨Computable.encode, Computable.of_nat _⟩
#align computable.eqv Computable.eqv

theorem Computable.equiv₂ (α β) [Denumerable α] [Denumerable β] :
    (Denumerable.equiv₂ α β).Computable :=
  (Computable.eqv _).trans (Computable.eqv _).symm
#align computable.equiv₂ Computable.equiv₂

theorem OneOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : OneOneEquiv (p ∘ e) p :=
  ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩
#align one_one_equiv.of_equiv OneOneEquiv.of_equiv

theorem ManyOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : ManyOneEquiv (p ∘ e) p :=
  (OneOneEquiv.of_equiv h).to_many_one
#align many_one_equiv.of_equiv ManyOneEquiv.of_equiv

theorem ManyOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) : p ≤₀ r ↔ q ≤₀ r :=
  ⟨h.2.trans, h.1.trans⟩
#align many_one_equiv.le_congr_left ManyOneEquiv.le_congr_left

theorem ManyOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) : p ≤₀ q ↔ p ≤₀ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
#align many_one_equiv.le_congr_right ManyOneEquiv.le_congr_right

theorem OneOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) : p ≤₁ r ↔ q ≤₁ r :=
  ⟨h.2.trans, h.1.trans⟩
#align one_one_equiv.le_congr_left OneOneEquiv.le_congr_left

theorem OneOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) : p ≤₁ q ↔ p ≤₁ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
#align one_one_equiv.le_congr_right OneOneEquiv.le_congr_right

theorem ManyOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv p q) :
    ManyOneEquiv p r ↔ ManyOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right
#align many_one_equiv.congr_left ManyOneEquiv.congr_left

theorem ManyOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) :
    ManyOneEquiv p q ↔ ManyOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left
#align many_one_equiv.congr_right ManyOneEquiv.congr_right

theorem OneOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv p q) :
    OneOneEquiv p r ↔ OneOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right
#align one_one_equiv.congr_left OneOneEquiv.congr_left

theorem OneOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop} (h : OneOneEquiv q r) :
    OneOneEquiv p q ↔ OneOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left
#align one_one_equiv.congr_right OneOneEquiv.congr_right

@[simp]
theorem Ulower.down_computable {α} [Primcodable α] : (Ulower.equiv α).Computable :=
  ⟨Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp⟩
#align ulower.down_computable Ulower.down_computable

theorem many_one_equiv_up {α} [Primcodable α] {p : α → Prop} : ManyOneEquiv (p ∘ Ulower.up) p :=
  ManyOneEquiv.of_equiv Ulower.down_computable.symm
#align many_one_equiv_up many_one_equiv_up

-- mathport name: «expr ⊕' »
local infixl:1001 " ⊕' " => Sum.elim

open Nat.Primrec

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `OneOneReducible.disjoin_left [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α `β] [] "}")
        (Term.instBinder "[" [] (Term.app `Primcodable [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Primcodable [`β]) "]")
        (Term.implicitBinder "{" [`p] [":" (Term.arrow `α "→" (Term.prop "Prop"))] "}")
        (Term.implicitBinder "{" [`q] [":" (Term.arrow `β "→" (Term.prop "Prop"))] "}")]
       (Term.typeSpec
        ":"
        (Computability.Reduce.«term_≤₁_» `p " ≤₁ " (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [`Sum.inl
         ","
         `Computable.sum_inl
         ","
         (Term.fun
          "fun"
          (Term.basicFun [`x `y] [] "=>" (Term.proj `Sum.inl.inj_iff "." (fieldIdx "1"))))
         ","
         (Term.fun "fun" (Term.basicFun [`a] [] "=>" `Iff.rfl))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`Sum.inl
        ","
        `Computable.sum_inl
        ","
        (Term.fun
         "fun"
         (Term.basicFun [`x `y] [] "=>" (Term.proj `Sum.inl.inj_iff "." (fieldIdx "1"))))
        ","
        (Term.fun "fun" (Term.basicFun [`a] [] "=>" `Iff.rfl))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `Iff.rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Iff.rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`x `y] [] "=>" (Term.proj `Sum.inl.inj_iff "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `Sum.inl.inj_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Sum.inl.inj_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Computable.sum_inl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Sum.inl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Computability.Reduce.«term_≤₁_» `p " ≤₁ " (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Computability.Reduce.term_⊕'_._@.Computability.Reduce._hyg.1239'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  OneOneReducible.disjoin_left
  { α β } [ Primcodable α ] [ Primcodable β ] { p : α → Prop } { q : β → Prop } : p ≤₁ p ⊕' q
  := ⟨ Sum.inl , Computable.sum_inl , fun x y => Sum.inl.inj_iff . 1 , fun a => Iff.rfl ⟩
#align one_one_reducible.disjoin_left OneOneReducible.disjoin_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `OneOneReducible.disjoin_right [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α `β] [] "}")
        (Term.instBinder "[" [] (Term.app `Primcodable [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Primcodable [`β]) "]")
        (Term.implicitBinder "{" [`p] [":" (Term.arrow `α "→" (Term.prop "Prop"))] "}")
        (Term.implicitBinder "{" [`q] [":" (Term.arrow `β "→" (Term.prop "Prop"))] "}")]
       (Term.typeSpec
        ":"
        (Computability.Reduce.«term_≤₁_» `q " ≤₁ " (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [`Sum.inr
         ","
         `Computable.sum_inr
         ","
         (Term.fun
          "fun"
          (Term.basicFun [`x `y] [] "=>" (Term.proj `Sum.inr.inj_iff "." (fieldIdx "1"))))
         ","
         (Term.fun "fun" (Term.basicFun [`a] [] "=>" `Iff.rfl))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`Sum.inr
        ","
        `Computable.sum_inr
        ","
        (Term.fun
         "fun"
         (Term.basicFun [`x `y] [] "=>" (Term.proj `Sum.inr.inj_iff "." (fieldIdx "1"))))
        ","
        (Term.fun "fun" (Term.basicFun [`a] [] "=>" `Iff.rfl))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `Iff.rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Iff.rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`x `y] [] "=>" (Term.proj `Sum.inr.inj_iff "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `Sum.inr.inj_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Sum.inr.inj_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Computable.sum_inr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Sum.inr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Computability.Reduce.«term_≤₁_» `q " ≤₁ " (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Computability.Reduce.term_⊕'_._@.Computability.Reduce._hyg.1239'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  OneOneReducible.disjoin_right
  { α β } [ Primcodable α ] [ Primcodable β ] { p : α → Prop } { q : β → Prop } : q ≤₁ p ⊕' q
  := ⟨ Sum.inr , Computable.sum_inr , fun x y => Sum.inr.inj_iff . 1 , fun a => Iff.rfl ⟩
#align one_one_reducible.disjoin_right OneOneReducible.disjoin_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `disjoin_many_one_reducible [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α `β `γ] [] "}")
        (Term.instBinder "[" [] (Term.app `Primcodable [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Primcodable [`β]) "]")
        (Term.instBinder "[" [] (Term.app `Primcodable [`γ]) "]")
        (Term.implicitBinder "{" [`p] [":" (Term.arrow `α "→" (Term.prop "Prop"))] "}")
        (Term.implicitBinder "{" [`q] [":" (Term.arrow `β "→" (Term.prop "Prop"))] "}")
        (Term.implicitBinder "{" [`r] [":" (Term.arrow `γ "→" (Term.prop "Prop"))] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Computability.Reduce.«term_≤₀_» `p " ≤₀ " `r)
         "→"
         (Term.arrow
          (Computability.Reduce.«term_≤₀_» `q " ≤₀ " `r)
          "→"
          (Computability.Reduce.«term_≤₀_»
           (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)
           " ≤₀ "
           `r)))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.anonymousCtor "⟨" [`f "," `c₁ "," `h₁] "⟩")
             ","
             (Term.anonymousCtor "⟨" [`g "," `c₂ "," `h₂] "⟩")]]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.app `Sum.elim [`f `g])
             ","
             (Term.app
              (Term.proj `Computable.id "." `sum_cases)
              [(Term.proj (Term.app (Term.proj `c₁ "." `comp) [`Computable.snd]) "." `to₂)
               (Term.proj (Term.app (Term.proj `c₂ "." `comp) [`Computable.snd]) "." `to₂)])
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.seq_focus
                    (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
                    "<;>"
                    "["
                    [(Tactic.apply "apply" `h₁) "," (Tactic.apply "apply" `h₂)]
                    "]")])))))]
            "⟩"))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `Sum.elim [`f `g])
        ","
        (Term.app
         (Term.proj `Computable.id "." `sum_cases)
         [(Term.proj (Term.app (Term.proj `c₁ "." `comp) [`Computable.snd]) "." `to₂)
          (Term.proj (Term.app (Term.proj `c₂ "." `comp) [`Computable.snd]) "." `to₂)])
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.seq_focus
               (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
               "<;>"
               "["
               [(Tactic.apply "apply" `h₁) "," (Tactic.apply "apply" `h₂)]
               "]")])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.seq_focus
             (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
             "<;>"
             "["
             [(Tactic.apply "apply" `h₁) "," (Tactic.apply "apply" `h₂)]
             "]")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.seq_focus
           (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
           "<;>"
           "["
           [(Tactic.apply "apply" `h₁) "," (Tactic.apply "apply" `h₂)]
           "]")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.seq_focus
       (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
       "<;>"
       "["
       [(Tactic.apply "apply" `h₁) "," (Tactic.apply "apply" `h₂)]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `h₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `h₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `x)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Computable.id "." `sum_cases)
       [(Term.proj (Term.app (Term.proj `c₁ "." `comp) [`Computable.snd]) "." `to₂)
        (Term.proj (Term.app (Term.proj `c₂ "." `comp) [`Computable.snd]) "." `to₂)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app (Term.proj `c₂ "." `comp) [`Computable.snd]) "." `to₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `c₂ "." `comp) [`Computable.snd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Computable.snd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `c₂ "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `c₂ "." `comp) [`Computable.snd])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app (Term.proj `c₁ "." `comp) [`Computable.snd]) "." `to₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `c₁ "." `comp) [`Computable.snd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Computable.snd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `c₁ "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `c₁ "." `comp) [`Computable.snd])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Computable.id "." `sum_cases)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Computable.id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Sum.elim [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Sum.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`g "," `c₂ "," `h₂] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`f "," `c₁ "," `h₁] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Computability.Reduce.«term_≤₀_» `p " ≤₀ " `r)
       "→"
       (Term.arrow
        (Computability.Reduce.«term_≤₀_» `q " ≤₀ " `r)
        "→"
        (Computability.Reduce.«term_≤₀_» (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q) " ≤₀ " `r)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Computability.Reduce.«term_≤₀_» `q " ≤₀ " `r)
       "→"
       (Computability.Reduce.«term_≤₀_» (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q) " ≤₀ " `r))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Computability.Reduce.«term_≤₀_» (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q) " ≤₀ " `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1001 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1000, term))
      (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Computability.Reduce.term_⊕'_._@.Computability.Reduce._hyg.1239'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  disjoin_many_one_reducible
  { α β γ }
      [ Primcodable α ]
      [ Primcodable β ]
      [ Primcodable γ ]
      { p : α → Prop }
      { q : β → Prop }
      { r : γ → Prop }
    : p ≤₀ r → q ≤₀ r → p ⊕' q ≤₀ r
  |
    ⟨ f , c₁ , h₁ ⟩ , ⟨ g , c₂ , h₂ ⟩
    =>
    ⟨
      Sum.elim f g
        ,
        Computable.id . sum_cases c₁ . comp Computable.snd . to₂ c₂ . comp Computable.snd . to₂
        ,
        fun x => by cases x <;> [ apply h₁ , apply h₂ ]
      ⟩
#align disjoin_many_one_reducible disjoin_many_one_reducible

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `disjoin_le [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α `β `γ] [] "}")
        (Term.instBinder "[" [] (Term.app `Primcodable [`α]) "]")
        (Term.instBinder "[" [] (Term.app `Primcodable [`β]) "]")
        (Term.instBinder "[" [] (Term.app `Primcodable [`γ]) "]")
        (Term.implicitBinder "{" [`p] [":" (Term.arrow `α "→" (Term.prop "Prop"))] "}")
        (Term.implicitBinder "{" [`q] [":" (Term.arrow `β "→" (Term.prop "Prop"))] "}")
        (Term.implicitBinder "{" [`r] [":" (Term.arrow `γ "→" (Term.prop "Prop"))] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         (Computability.Reduce.«term_≤₀_» (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q) " ≤₀ " `r)
         "↔"
         («term_∧_»
          (Computability.Reduce.«term_≤₀_» `p " ≤₀ " `r)
          "∧"
          (Computability.Reduce.«term_≤₀_» `q " ≤₀ " `r)))))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              (Term.proj (Term.proj `OneOneReducible.disjoin_left "." `to_many_one) "." `trans)
              [`h])
             ","
             (Term.app
              (Term.proj (Term.proj `OneOneReducible.disjoin_right "." `to_many_one) "." `trans)
              [`h])]
            "⟩")))
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
           []
           "=>"
           (Term.app `disjoin_many_one_reducible [`h₁ `h₂])))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.app
             (Term.proj (Term.proj `OneOneReducible.disjoin_left "." `to_many_one) "." `trans)
             [`h])
            ","
            (Term.app
             (Term.proj (Term.proj `OneOneReducible.disjoin_right "." `to_many_one) "." `trans)
             [`h])]
           "⟩")))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
          []
          "=>"
          (Term.app `disjoin_many_one_reducible [`h₁ `h₂])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")]
        []
        "=>"
        (Term.app `disjoin_many_one_reducible [`h₁ `h₂])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `disjoin_many_one_reducible [`h₁ `h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `disjoin_many_one_reducible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`h₁ "," `h₂] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.app
           (Term.proj (Term.proj `OneOneReducible.disjoin_left "." `to_many_one) "." `trans)
           [`h])
          ","
          (Term.app
           (Term.proj (Term.proj `OneOneReducible.disjoin_right "." `to_many_one) "." `trans)
           [`h])]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         (Term.proj (Term.proj `OneOneReducible.disjoin_left "." `to_many_one) "." `trans)
         [`h])
        ","
        (Term.app
         (Term.proj (Term.proj `OneOneReducible.disjoin_right "." `to_many_one) "." `trans)
         [`h])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `OneOneReducible.disjoin_right "." `to_many_one) "." `trans)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `OneOneReducible.disjoin_right "." `to_many_one) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `OneOneReducible.disjoin_right "." `to_many_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `OneOneReducible.disjoin_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `OneOneReducible.disjoin_left "." `to_many_one) "." `trans)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `OneOneReducible.disjoin_left "." `to_many_one) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `OneOneReducible.disjoin_left "." `to_many_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `OneOneReducible.disjoin_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       (Computability.Reduce.«term_≤₀_» (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q) " ≤₀ " `r)
       "↔"
       («term_∧_»
        (Computability.Reduce.«term_≤₀_» `p " ≤₀ " `r)
        "∧"
        (Computability.Reduce.«term_≤₀_» `q " ≤₀ " `r)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       (Computability.Reduce.«term_≤₀_» `p " ≤₀ " `r)
       "∧"
       (Computability.Reduce.«term_≤₀_» `q " ≤₀ " `r))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Computability.Reduce.«term_≤₀_» `q " ≤₀ " `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1001 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1000, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1000 >? 1024, (none,
     [anonymous]) <=? (some 1000, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1000, (some 1001,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Computability.Reduce.«term_≤₀_» `p " ≤₀ " `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1001 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1000, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1000 >? 1024, (none,
     [anonymous]) <=? (some 1000, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1000, (some 1001, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Computability.Reduce.«term_≤₀_» (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q) " ≤₀ " `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1001 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1000, term))
      (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Computability.Reduce.term_⊕'_._@.Computability.Reduce._hyg.1239'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  disjoin_le
  { α β γ }
      [ Primcodable α ]
      [ Primcodable β ]
      [ Primcodable γ ]
      { p : α → Prop }
      { q : β → Prop }
      { r : γ → Prop }
    : p ⊕' q ≤₀ r ↔ p ≤₀ r ∧ q ≤₀ r
  :=
    ⟨
      fun
          h
            =>
            ⟨
              OneOneReducible.disjoin_left . to_many_one . trans h
                ,
                OneOneReducible.disjoin_right . to_many_one . trans h
              ⟩
        ,
        fun ⟨ h₁ , h₂ ⟩ => disjoin_many_one_reducible h₁ h₂
      ⟩
#align disjoin_le disjoin_le

variable {α : Type u} [Primcodable α] [Inhabited α]

variable {β : Type v} [Primcodable β] [Inhabited β]

variable {γ : Type w} [Primcodable γ] [Inhabited γ]

/-- Computable and injective mapping of predicates to sets of natural numbers.
-/
def toNat (p : Set α) : Set ℕ :=
  { n | p ((Encodable.decode α n).getOrElse default) }
#align to_nat toNat

@[simp]
theorem to_nat_many_one_reducible {p : Set α} : toNat p ≤₀ p :=
  ⟨fun n => (Encodable.decode α n).getOrElse default,
    Computable.option_get_or_else Computable.decode (Computable.const _), fun _ => Iff.rfl⟩
#align to_nat_many_one_reducible to_nat_many_one_reducible

@[simp]
theorem many_one_reducible_to_nat {p : Set α} : p ≤₀ toNat p :=
  ⟨Encodable.encode, Computable.encode, by simp [toNat, setOf]⟩
#align many_one_reducible_to_nat many_one_reducible_to_nat

@[simp]
theorem many_one_reducible_to_nat_to_nat {p : Set α} {q : Set β} : toNat p ≤₀ toNat q ↔ p ≤₀ q :=
  ⟨fun h => many_one_reducible_to_nat.trans (h.trans to_nat_many_one_reducible), fun h =>
    to_nat_many_one_reducible.trans (h.trans many_one_reducible_to_nat)⟩
#align many_one_reducible_to_nat_to_nat many_one_reducible_to_nat_to_nat

@[simp]
theorem to_nat_many_one_equiv {p : Set α} : ManyOneEquiv (toNat p) p := by simp [ManyOneEquiv]
#align to_nat_many_one_equiv to_nat_many_one_equiv

@[simp]
theorem many_one_equiv_to_nat (p : Set α) (q : Set β) :
    ManyOneEquiv (toNat p) (toNat q) ↔ ManyOneEquiv p q := by simp [ManyOneEquiv]
#align many_one_equiv_to_nat many_one_equiv_to_nat

/-- A many-one degree is an equivalence class of sets up to many-one equivalence. -/
def ManyOneDegree : Type :=
  Quotient (⟨ManyOneEquiv, equivalence_of_many_one_equiv⟩ : Setoid (Set ℕ))
#align many_one_degree ManyOneDegree

namespace ManyOneDegree

/-- The many-one degree of a set on a primcodable type. -/
def of (p : α → Prop) : ManyOneDegree :=
  Quotient.mk' (toNat p)
#align many_one_degree.of ManyOneDegree.of

@[elab_as_elim]
protected theorem ind_on {C : ManyOneDegree → Prop} (d : ManyOneDegree)
    (h : ∀ p : Set ℕ, C (of p)) : C d :=
  Quotient.inductionOn' d h
#align many_one_degree.ind_on ManyOneDegree.ind_on

/-- Lifts a function on sets of natural numbers to many-one degrees.
-/
@[elab_as_elim, reducible]
protected def liftOn {φ} (d : ManyOneDegree) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : φ :=
  Quotient.liftOn' d f h
#align many_one_degree.lift_on ManyOneDegree.liftOn

@[simp]
protected theorem lift_on_eq {φ} (p : Set ℕ) (f : Set ℕ → φ)
    (h : ∀ p q, ManyOneEquiv p q → f p = f q) : (of p).liftOn f h = f p :=
  rfl
#align many_one_degree.lift_on_eq ManyOneDegree.lift_on_eq

/-- Lifts a binary function on sets of natural numbers to many-one degrees.
-/
@[elab_as_elim, reducible, simp]
protected def liftOn₂ {φ} (d₁ d₂ : ManyOneDegree) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) : φ :=
  d₁.liftOn (fun p => d₂.liftOn (f p) fun q₁ q₂ hq => h _ _ _ _ (by rfl) hq)
    (by
      intro p₁ p₂ hp
      induction d₂ using ManyOneDegree.ind_on
      apply h
      assumption
      rfl)
#align many_one_degree.lift_on₂ ManyOneDegree.liftOn₂

@[simp]
protected theorem lift_on₂_eq {φ} (p q : Set ℕ) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) :
    (of p).liftOn₂ (of q) f h = f p q :=
  rfl
#align many_one_degree.lift_on₂_eq ManyOneDegree.lift_on₂_eq

@[simp]
theorem of_eq_of {p : α → Prop} {q : β → Prop} : of p = of q ↔ ManyOneEquiv p q := by
  simp [of, Quotient.eq']
#align many_one_degree.of_eq_of ManyOneDegree.of_eq_of

instance : Inhabited ManyOneDegree :=
  ⟨of (∅ : Set ℕ)⟩

/-- For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one reducible to the
sets in `d₂`.
-/
instance : LE ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    (ManyOneDegree.liftOn₂ d₁ d₂ (· ≤₀ ·)) fun p₁ p₂ q₁ q₂ hp hq =>
      propext (hp.le_congr_left.trans hq.le_congr_right)⟩

@[simp]
theorem of_le_of {p : α → Prop} {q : β → Prop} : of p ≤ of q ↔ p ≤₀ q :=
  many_one_reducible_to_nat_to_nat
#align many_one_degree.of_le_of ManyOneDegree.of_le_of

private theorem le_refl (d : ManyOneDegree) : d ≤ d := by
  induction d using ManyOneDegree.ind_on <;> simp
#align many_one_degree.le_refl many_one_degree.le_refl

private theorem le_antisymm {d₁ d₂ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ :=
  by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  intro hp hq
  simp_all only [ManyOneEquiv, of_le_of, of_eq_of, true_and_iff]
#align many_one_degree.le_antisymm many_one_degree.le_antisymm

private theorem le_trans {d₁ d₂ d₃ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ :=
  by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  apply ManyOneReducible.trans
#align many_one_degree.le_trans many_one_degree.le_trans

instance : PartialOrder ManyOneDegree where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The join of two degrees, induced by the disjoint union of two underlying sets. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig [] (Term.typeSpec ":" (Term.app `Add [`ManyOneDegree])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`d₁ `d₂]
           []
           "=>"
           (Term.app
            (Term.proj `d₁ "." `liftOn₂)
            [`d₂
             (Term.fun
              "fun"
              (Term.basicFun
               [`a `b]
               []
               "=>"
               (Term.app `of [(Computability.Reduce.«term_⊕'_» `a " ⊕' " `b)])))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `c))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `d))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₁)])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₂)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₂)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_eq_of)] "]") [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app
                     `disjoin_many_one_reducible
                     [(Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
                      (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
                    ","
                    (Term.app
                     `disjoin_many_one_reducible
                     [(Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
                      (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])])]
                   "⟩"))])))])))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`d₁ `d₂]
          []
          "=>"
          (Term.app
           (Term.proj `d₁ "." `liftOn₂)
           [`d₂
            (Term.fun
             "fun"
             (Term.basicFun
              [`a `b]
              []
              "=>"
              (Term.app `of [(Computability.Reduce.«term_⊕'_» `a " ⊕' " `b)])))
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Std.Tactic.rintro
                 "rintro"
                 [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
                  (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
                  (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `c))
                  (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `d))
                  (Std.Tactic.RCases.rintroPat.one
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₁)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₁)])
                      [])]
                    "⟩"))
                  (Std.Tactic.RCases.rintroPat.one
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₂)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₂)])
                      [])]
                    "⟩"))]
                 [])
                []
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_eq_of)] "]") [])
                []
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app
                    `disjoin_many_one_reducible
                    [(Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
                     (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
                   ","
                   (Term.app
                    `disjoin_many_one_reducible
                    [(Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
                     (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])])]
                  "⟩"))])))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`d₁ `d₂]
        []
        "=>"
        (Term.app
         (Term.proj `d₁ "." `liftOn₂)
         [`d₂
          (Term.fun
           "fun"
           (Term.basicFun
            [`a `b]
            []
            "=>"
            (Term.app `of [(Computability.Reduce.«term_⊕'_» `a " ⊕' " `b)])))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.rintro
               "rintro"
               [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
                (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
                (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `c))
                (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `d))
                (Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₁)])
                    [])]
                  "⟩"))
                (Std.Tactic.RCases.rintroPat.one
                 (Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₂)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₂)])
                    [])]
                  "⟩"))]
               [])
              []
              (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_eq_of)] "]") [])
              []
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [(Term.app
                  `disjoin_many_one_reducible
                  [(Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
                   (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
                 ","
                 (Term.app
                  `disjoin_many_one_reducible
                  [(Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
                   (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])])]
                "⟩"))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `d₁ "." `liftOn₂)
       [`d₂
        (Term.fun
         "fun"
         (Term.basicFun
          [`a `b]
          []
          "=>"
          (Term.app `of [(Computability.Reduce.«term_⊕'_» `a " ⊕' " `b)])))
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `c))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `d))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₁)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₂)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_eq_of)] "]") [])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.app
                `disjoin_many_one_reducible
                [(Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
                 (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
               ","
               (Term.app
                `disjoin_many_one_reducible
                [(Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
                 (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])])]
              "⟩"))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `c))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `d))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₁)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₂)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₂)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_eq_of)] "]") [])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              `disjoin_many_one_reducible
              [(Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
               (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
             ","
             (Term.app
              `disjoin_many_one_reducible
              [(Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
               (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])])]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `disjoin_many_one_reducible
          [(Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
           (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
         ","
         (Term.app
          `disjoin_many_one_reducible
          [(Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
           (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `disjoin_many_one_reducible
         [(Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
          (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
        ","
        (Term.app
         `disjoin_many_one_reducible
         [(Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
          (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `disjoin_many_one_reducible
       [(Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
        (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_one_reducible.disjoin_right.to_many_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hr₂.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_one_reducible.disjoin_left.to_many_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hr₁.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `disjoin_many_one_reducible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `disjoin_many_one_reducible
       [(Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
        (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_one_reducible.disjoin_right.to_many_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hl₂.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_one_reducible.disjoin_left.to_many_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hl₁.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `disjoin_many_one_reducible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_eq_of)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_eq_of
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `c))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `d))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₁)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₁)])
            [])]
          "⟩"))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₂)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₂)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Std.Tactic.rintro
          "rintro"
          [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `a))
           (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `b))
           (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `c))
           (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `d))
           (Std.Tactic.RCases.rintroPat.one
            (Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₁)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₁)])
               [])]
             "⟩"))
           (Std.Tactic.RCases.rintroPat.one
            (Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hl₂)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr₂)])
               [])]
             "⟩"))]
          [])
         []
         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `of_eq_of)] "]") [])
         []
         (Tactic.exact
          "exact"
          (Term.anonymousCtor
           "⟨"
           [(Term.app
             `disjoin_many_one_reducible
             [(Term.paren
               "("
               (Term.app `hl₁.trans [`one_one_reducible.disjoin_left.to_many_one])
               ")")
              (Term.paren
               "("
               (Term.app `hl₂.trans [`one_one_reducible.disjoin_right.to_many_one])
               ")")])
            ","
            (Term.app
             `disjoin_many_one_reducible
             [(Term.paren
               "("
               (Term.app `hr₁.trans [`one_one_reducible.disjoin_left.to_many_one])
               ")")
              (Term.paren
               "("
               (Term.app `hr₂.trans [`one_one_reducible.disjoin_right.to_many_one])
               ")")])]
           "⟩"))])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b]
        []
        "=>"
        (Term.app `of [(Computability.Reduce.«term_⊕'_» `a " ⊕' " `b)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `of [(Computability.Reduce.«term_⊕'_» `a " ⊕' " `b)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Computability.Reduce.«term_⊕'_» `a " ⊕' " `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Computability.Reduce.term_⊕'_._@.Computability.Reduce._hyg.1239'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The join of two degrees, induced by the disjoint union of two underlying sets. -/
  instance
    : Add ManyOneDegree
    :=
      ⟨
        fun
          d₁ d₂
            =>
            d₁ . liftOn₂
              d₂
                fun a b => of a ⊕' b
                by
                  rintro a b c d ⟨ hl₁ , hr₁ ⟩ ⟨ hl₂ , hr₂ ⟩
                    rw [ of_eq_of ]
                    exact
                      ⟨
                        disjoin_many_one_reducible
                            hl₁.trans one_one_reducible.disjoin_left.to_many_one
                              hl₂.trans one_one_reducible.disjoin_right.to_many_one
                          ,
                          disjoin_many_one_reducible
                            hr₁.trans one_one_reducible.disjoin_left.to_many_one
                              hr₂.trans one_one_reducible.disjoin_right.to_many_one
                        ⟩
        ⟩

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
      (Command.declId `add_of [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p] [":" (Term.app `Set [`α])] [] ")")
        (Term.explicitBinder "(" [`q] [":" (Term.app `Set [`β])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `of [(Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)])
         "="
         («term_+_» (Term.app `of [`p]) "+" (Term.app `of [`q])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `of_eq_of "." `mpr)
        [(Term.anonymousCtor
          "⟨"
          [(Term.app
            `disjoin_many_one_reducible
            [(Term.app
              (Term.proj `many_one_reducible_to_nat "." `trans)
              [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
             (Term.app
              (Term.proj `many_one_reducible_to_nat "." `trans)
              [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])])
           ","
           (Term.app
            `disjoin_many_one_reducible
            [(Term.app
              (Term.proj `to_nat_many_one_reducible "." `trans)
              [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
             (Term.app
              (Term.proj `to_nat_many_one_reducible "." `trans)
              [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])])]
          "⟩")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `of_eq_of "." `mpr)
       [(Term.anonymousCtor
         "⟨"
         [(Term.app
           `disjoin_many_one_reducible
           [(Term.app
             (Term.proj `many_one_reducible_to_nat "." `trans)
             [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
            (Term.app
             (Term.proj `many_one_reducible_to_nat "." `trans)
             [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])])
          ","
          (Term.app
           `disjoin_many_one_reducible
           [(Term.app
             (Term.proj `to_nat_many_one_reducible "." `trans)
             [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
            (Term.app
             (Term.proj `to_nat_many_one_reducible "." `trans)
             [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `disjoin_many_one_reducible
         [(Term.app
           (Term.proj `many_one_reducible_to_nat "." `trans)
           [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
          (Term.app
           (Term.proj `many_one_reducible_to_nat "." `trans)
           [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])])
        ","
        (Term.app
         `disjoin_many_one_reducible
         [(Term.app
           (Term.proj `to_nat_many_one_reducible "." `trans)
           [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
          (Term.app
           (Term.proj `to_nat_many_one_reducible "." `trans)
           [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `disjoin_many_one_reducible
       [(Term.app
         (Term.proj `to_nat_many_one_reducible "." `trans)
         [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
        (Term.app
         (Term.proj `to_nat_many_one_reducible "." `trans)
         [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `to_nat_many_one_reducible "." `trans)
       [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `OneOneReducible.disjoin_right "." `to_many_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `OneOneReducible.disjoin_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `to_nat_many_one_reducible "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `to_nat_many_one_reducible
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `to_nat_many_one_reducible "." `trans)
      [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `to_nat_many_one_reducible "." `trans)
       [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `OneOneReducible.disjoin_left "." `to_many_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `OneOneReducible.disjoin_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `to_nat_many_one_reducible "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `to_nat_many_one_reducible
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `to_nat_many_one_reducible "." `trans)
      [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `disjoin_many_one_reducible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `disjoin_many_one_reducible
       [(Term.app
         (Term.proj `many_one_reducible_to_nat "." `trans)
         [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
        (Term.app
         (Term.proj `many_one_reducible_to_nat "." `trans)
         [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `many_one_reducible_to_nat "." `trans)
       [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `OneOneReducible.disjoin_right "." `to_many_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `OneOneReducible.disjoin_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `many_one_reducible_to_nat "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `many_one_reducible_to_nat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `many_one_reducible_to_nat "." `trans)
      [(Term.proj `OneOneReducible.disjoin_right "." `to_many_one)])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `many_one_reducible_to_nat "." `trans)
       [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `OneOneReducible.disjoin_left "." `to_many_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `OneOneReducible.disjoin_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `many_one_reducible_to_nat "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `many_one_reducible_to_nat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `many_one_reducible_to_nat "." `trans)
      [(Term.proj `OneOneReducible.disjoin_left "." `to_many_one)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `disjoin_many_one_reducible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `of_eq_of "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `of_eq_of
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `of [(Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)])
       "="
       («term_+_» (Term.app `of [`p]) "+" (Term.app `of [`q])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app `of [`p]) "+" (Term.app `of [`q]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `of [`q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `of [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `of [(Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Computability.Reduce.«term_⊕'_» `p " ⊕' " `q)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Computability.Reduce.«term_⊕'_»', expected 'Computability.Reduce.term_⊕'_._@.Computability.Reduce._hyg.1239'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    add_of
    ( p : Set α ) ( q : Set β ) : of p ⊕' q = of p + of q
    :=
      of_eq_of . mpr
        ⟨
          disjoin_many_one_reducible
              many_one_reducible_to_nat . trans OneOneReducible.disjoin_left . to_many_one
                many_one_reducible_to_nat . trans OneOneReducible.disjoin_right . to_many_one
            ,
            disjoin_many_one_reducible
              to_nat_many_one_reducible . trans OneOneReducible.disjoin_left . to_many_one
                to_nat_many_one_reducible . trans OneOneReducible.disjoin_right . to_many_one
          ⟩
#align many_one_degree.add_of ManyOneDegree.add_of

@[simp]
protected theorem add_le {d₁ d₂ d₃ : ManyOneDegree} : d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃ :=
  by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  simpa only [← add_of, of_le_of] using disjoin_le
#align many_one_degree.add_le ManyOneDegree.add_le

@[simp]
protected theorem le_add_left (d₁ d₂ : ManyOneDegree) : d₁ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (by rfl)).1
#align many_one_degree.le_add_left ManyOneDegree.le_add_left

@[simp]
protected theorem le_add_right (d₁ d₂ : ManyOneDegree) : d₂ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (by rfl)).2
#align many_one_degree.le_add_right ManyOneDegree.le_add_right

instance : SemilatticeSup ManyOneDegree :=
  { ManyOneDegree.partialOrder with
    sup := (· + ·)
    le_sup_left := ManyOneDegree.le_add_left
    le_sup_right := ManyOneDegree.le_add_right
    sup_le := fun a b c h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }

end ManyOneDegree

