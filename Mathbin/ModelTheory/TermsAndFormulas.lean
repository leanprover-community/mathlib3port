/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathbin.Data.Finset.Basic
import Mathbin.ModelTheory.Basic

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language.term` is defined so that `L.term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `first_order.language.formula` is defined so that `L.formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `first_order.language.sentence` is a formula with no free variables.
* A `first_order.language.Theory` is a set of sentences.
* `first_order.language.Theory.is_satisfiable` indicates that a theory has a nonempty model.
* Given a theory `T`, `first_order.language.Theory.semantically_equivalent` defines an equivalence
relation `T.semantically_equivalent` on formulas of a particular signature, indicating that the
formulas have the same realization in models of `T`. (This is more often known as logical
equivalence once it is known that this is equivalent to the proof-theoretic definition.)

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

open_locale FirstOrder

open Structure

variable (L)

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term (α : Type) : Type u
  | var {} : ∀ a : α, term
  | func {} : ∀ {l : ℕ} f : L.Functions l ts : Finₓ l → term, term

export Term ()

variable {L}

/-- Relabels a term's variables along a particular function. -/
@[simp]
def Term.relabel {α β : Type} (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun i => (ts i).relabel

instance {α : Type} [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩

instance {α} : Coe L.const (L.Term α) :=
  ⟨fun c => func c finZeroElim⟩

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
@[simp]
def realizeTermₓ {α : Type} (v : α → M) : ∀ t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => realize_term (ts i)

@[simp]
theorem realize_term_relabel {α β : Type} (g : α → β) (v : β → M) (t : L.Term α) :
    realizeTermₓ v (t.relabel g) = realizeTermₓ (v ∘ g) t := by
  induction' t with _ n f ts ih
  · rfl
    
  · simp [ih]
    

@[simp]
theorem Hom.realize_term {α : Type} (v : α → M) (t : L.Term α) (g : M →[L] N) :
    realizeTermₓ (g ∘ v) t = g (realizeTermₓ v t) := by
  induction t
  · rfl
    
  · rw [realize_term, realize_term, g.map_fun]
    refine' congr rfl _
    ext x
    simp [t_ih x]
    

@[simp]
theorem Embedding.realize_term {α : Type} (v : α → M) (t : L.Term α) (g : M ↪[L] N) :
    realizeTermₓ (g ∘ v) t = g (realizeTermₓ v t) :=
  g.toHom.realizeTerm v t

@[simp]
theorem Equiv.realize_term {α : Type} (v : α → M) (t : L.Term α) (g : M ≃[L] N) :
    realizeTermₓ (g ∘ v) t = g (realizeTermₓ v t) :=
  g.toHom.realizeTerm v t

variable (L)

/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BoundedFormula (α : Type) : ℕ → Type max u v
  | bd_falsum {} {n} : bounded_formula n
  | bd_equal {n} (t₁ t₂ : L.Term (Sum α (Finₓ n))) : bounded_formula n
  | bd_rel {n l : ℕ} (R : L.Relations l) (ts : Finₓ l → L.Term (Sum α (Finₓ n))) : bounded_formula n
  | bd_imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
  | bd_all {n} (f : bounded_formula (n + 1)) : bounded_formula n

export BoundedFormula ()

instance {α : Type} {n : ℕ} : Inhabited (L.BoundedFormula α n) :=
  ⟨bd_falsum⟩

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible]
def Formula (α : Type) :=
  L.BoundedFormula α 0

/-- A sentence is a formula with no free variables. -/
@[reducible]
def Sentence :=
  L.Formula Pempty

/-- A theory is a set of sentences. -/
@[reducible]
def Theory :=
  Set L.Sentence

variable {L} {α : Type}

section Formula

variable {n : ℕ}

@[simps]
instance : HasBot (L.BoundedFormula α n) :=
  ⟨bd_falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[reducible]
def bdNot (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  bd_imp φ ⊥

@[simps]
instance : HasTop (L.BoundedFormula α n) :=
  ⟨bdNot bd_falsum⟩

@[simps]
instance : HasInf (L.BoundedFormula α n) :=
  ⟨fun f g => bdNot (bd_imp f (bdNot g))⟩

@[simps]
instance : HasSup (L.BoundedFormula α n) :=
  ⟨fun f g => bd_imp (bdNot f) g⟩

/-- Relabels a bounded formula's variables along a particular function. -/
@[simp]
def BoundedFormula.relabel {α β : Type} (g : α → β) : ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormula β n
  | n, bd_falsum => bd_falsum
  | n, bd_equal t₁ t₂ =>
    bd_equal (t₁.relabel (Sum.elim (Sum.inl ∘ g) Sum.inr)) (t₂.relabel (Sum.elim (Sum.inl ∘ g) Sum.inr))
  | n, bd_rel R ts => bd_rel R (Term.relabel (Sum.elim (Sum.inl ∘ g) Sum.inr) ∘ ts)
  | n, bd_imp f₁ f₂ => bd_imp f₁.relabel f₂.relabel
  | n, bd_all f => bd_all f.relabel

namespace Formula

/-- The equality of two terms as a first-order formula. -/
def equal (t₁ t₂ : L.Term α) : L.Formula α :=
  bd_equal (t₁.relabel Sum.inl) (t₂.relabel Sum.inl)

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions n) : L.Formula (Finₓ (n + 1)) :=
  equal (func f fun i => var i) (var n)

end Formula

end Formula

variable {L}

instance nonempty_bounded_formula {α : Type} (n : ℕ) : Nonempty <| L.BoundedFormula α n :=
  Nonempty.intro
    (by
      constructor)

variable (M)

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[simp]
def RealizeBoundedFormulaₓ : ∀ {l} f : L.BoundedFormula α l v : α → M xs : Finₓ l → M, Prop
  | _, bd_falsum, v, xs => False
  | _, bd_equal t₁ t₂, v, xs => realizeTermₓ (Sum.elim v xs) t₁ = realizeTermₓ (Sum.elim v xs) t₂
  | _, bd_rel R ts, v, xs => RelMap R fun i => realizeTermₓ (Sum.elim v xs) (ts i)
  | _, bd_imp f₁ f₂, v, xs => realize_bounded_formula f₁ v xs → realize_bounded_formula f₂ v xs
  | _, bd_all f, v, xs => ∀ x : M, realize_bounded_formula f v (Finₓ.cons x xs)

@[simp]
theorem realize_not {l} (f : L.BoundedFormula α l) (v : α → M) (xs : Finₓ l → M) :
    RealizeBoundedFormulaₓ M (bdNot f) v xs = ¬RealizeBoundedFormulaₓ M f v xs :=
  rfl

theorem realize_inf {l} (φ ψ : L.BoundedFormula α l) (v : α → M) (xs : Finₓ l → M) :
    RealizeBoundedFormulaₓ M (φ⊓ψ) v xs = (RealizeBoundedFormulaₓ M φ v xs ∧ RealizeBoundedFormulaₓ M ψ v xs) := by
  simp

theorem realize_imp {l} (φ ψ : L.BoundedFormula α l) (v : α → M) (xs : Finₓ l → M) :
    RealizeBoundedFormulaₓ M (φ.bd_imp ψ) v xs = (RealizeBoundedFormulaₓ M φ v xs → RealizeBoundedFormulaₓ M ψ v xs) :=
  by
  simp only [realize_bounded_formula]

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[reducible]
def RealizeFormula (f : L.Formula α) (v : α → M) : Prop :=
  RealizeBoundedFormulaₓ M f v finZeroElim

/-- A sentence can be evaluated as true or false in a structure. -/
@[reducible]
def RealizeSentence (φ : L.Sentence) : Prop :=
  RealizeFormula M φ Pempty.elimₓ

-- mathport name: «expr ⊨ »
infixl:51 " ⊨ " => RealizeSentence

/-- A model of a theory is a structure in which every sentence is realized as true. -/
-- input using \|= or \vDash, but not using \models
@[reducible]
def Theory.Model (T : L.Theory) : Prop :=
  ∀, ∀ φ ∈ T, ∀, RealizeSentence M φ

-- mathport name: «expr ⊨ »
infixl:51 " ⊨ " => Theory.Model

-- input using \|= or \vDash, but not using \models
variable {M}

theorem Theory.Model.mono {T T' : L.Theory} (h : T'.Model M) (hs : T ⊆ T') : T.Model M := fun φ hφ => h φ (hs hφ)

@[simp]
theorem realize_bounded_formula_relabel {α β : Type} {n : ℕ} (g : α → β) (v : β → M) (xs : Finₓ n → M)
    (φ : L.BoundedFormula α n) : RealizeBoundedFormulaₓ M (φ.relabel g) v xs ↔ RealizeBoundedFormulaₓ M φ (v ∘ g) xs :=
  by
  have h : ∀ m : ℕ xs' : Finₓ m → M, Sum.elim v xs' ∘ Sum.elim (Sum.inl ∘ g) Sum.inr = Sum.elim (v ∘ g) xs' := by
    intro m xs'
    ext x
    cases x <;> simp
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp [h _ xs]
    
  · simp [h _ xs]
    
  · simp [ih1, ih2]
    
  · simp [ih3]
    

@[simp]
theorem Equiv.realize_bounded_formula {α : Type} {n : ℕ} (v : α → M) (xs : Finₓ n → M) (φ : L.BoundedFormula α n)
    (g : M ≃[L] N) : RealizeBoundedFormulaₓ N φ (g ∘ v) (g ∘ xs) ↔ RealizeBoundedFormulaₓ M φ v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp only [realize_bounded_formula, ← Sum.comp_elim, equiv.realize_term, g.injective.eq_iff]
    
  · simp only [realize_bounded_formula, ← Sum.comp_elim, equiv.realize_term, g.map_rel]
    
  · rw [realize_bounded_formula, ih1, ih2, realize_bounded_formula]
    
  · rw [realize_bounded_formula, realize_bounded_formula]
    constructor
    · intro h a
      have h' := h (g a)
      rw [← Finₓ.comp_cons, ih3] at h'
      exact h'
      
    · intro h a
      have h' := h (g.symm a)
      rw [← ih3, Finₓ.comp_cons, g.apply_symm_apply] at h'
      exact h'
      
    

@[simp]
theorem realize_formula_relabel {α β : Type} (g : α → β) (v : β → M) (φ : L.Formula α) :
    RealizeFormula M (φ.relabel g) v ↔ RealizeFormula M φ (v ∘ g) := by
  rw [realize_formula, realize_formula, realize_bounded_formula_relabel]

@[simp]
theorem realize_formula_equiv {α : Type} (v : α → M) (φ : L.Formula α) (g : M ≃[L] N) :
    RealizeFormula N φ (g ∘ v) ↔ RealizeFormula M φ v := by
  rw [realize_formula, realize_formula, ← equiv.realize_bounded_formula v finZeroElim φ g, iff_eq_eq]
  exact congr rfl (funext finZeroElim)

@[simp]
theorem realize_equal {α : Type _} (t₁ t₂ : L.Term α) (x : α → M) :
    RealizeFormula M (Formula.equal t₁ t₂) x ↔ realizeTermₓ x t₁ = realizeTermₓ x t₂ := by
  simp [formula.equal, realize_formula]

@[simp]
theorem realize_graph {l : ℕ} (f : L.Functions l) (x : Finₓ l → M) (y : M) :
    RealizeFormula M (Formula.graph f) (Finₓ.snoc x y) ↔ funMap f x = y := by
  simp only [formula.graph, realize_term, Finₓ.coe_eq_cast_succ, realize_equal, Finₓ.snoc_cast_succ]
  rw [Finₓ.coe_nat_eq_last, Finₓ.snoc_last]

namespace Theory

/-- A theory is satisfiable if a structure models it. -/
def IsSatisfiable (T : L.Theory) : Prop :=
  ∃ (M : Type max u v)(_ : Nonempty M)(str : L.Structure M), @Theory.Model L M str T

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def IsFinitelySatisfiable (T : L.Theory) : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → (T0 : L.Theory).IsSatisfiable

/-- Given that a theory is satisfiable, selects a model using choice. -/
def IsSatisfiable.SomeModel {T : L.Theory} (h : T.IsSatisfiable) : Type _ :=
  Classical.some h

instance IsSatisfiable.nonempty_some_model {T : L.Theory} (h : T.IsSatisfiable) : Nonempty h.SomeModel :=
  Classical.some (Classical.some_spec h)

noncomputable instance IsSatisfiable.inhabitedSomeModel {T : L.Theory} (h : T.IsSatisfiable) : Inhabited h.SomeModel :=
  Classical.inhabitedOfNonempty'

noncomputable instance IsSatisfiable.someModelStructure {T : L.Theory} (h : T.IsSatisfiable) :
    L.Structure h.SomeModel :=
  Classical.some (Classical.some_spec (Classical.some_spec h))

theorem IsSatisfiable.some_model_models {T : L.Theory} (h : T.IsSatisfiable) : T.Model h.SomeModel :=
  Classical.some_spec (Classical.some_spec (Classical.some_spec h))

theorem Model.is_satisfiable {T : L.Theory} (M : Type max u v) [n : Nonempty M] [S : L.Structure M] (h : T.Model M) :
    T.IsSatisfiable :=
  ⟨M, n, S, h⟩

theorem IsSatisfiable.mono {T T' : L.Theory} (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
  ⟨h.SomeModel, h.nonempty_some_model, h.someModelStructure, h.some_model_models.mono hs⟩

theorem IsSatisfiable.is_finitely_satisfiable {T : L.Theory} (h : T.IsSatisfiable) : T.IsFinitelySatisfiable := fun _ =>
  h.mono

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def ModelsBoundedFormula {n : ℕ} {α : Type} (T : L.Theory) (φ : L.BoundedFormula α n) : Prop :=
  ∀ M : Type max u v [Nonempty M] [str : L.Structure M] v : α → M xs : Finₓ n → M,
    @Theory.Model L M str T → @RealizeBoundedFormulaₓ L M str α n φ v xs

-- mathport name: «expr ⊨ »
infixl:51 " ⊨ " => ModelsBoundedFormula

-- input using \|= or \vDash, but not using \models
theorem models_formula_iff {α : Type} (T : L.Theory) (φ : L.Formula α) :
    T ⊨ φ ↔
      ∀ M : Type max u v [Nonempty M] [str : L.Structure M] v : α → M,
        @Theory.Model L M str T → @RealizeFormula L M str α φ v :=
  by
  refine'
    forall_congrₓ fun M =>
      forall_congrₓ fun ne => forall_congrₓ fun str => forall_congrₓ fun v => ⟨fun h => h finZeroElim, fun h xs => _⟩
  rw [Subsingleton.elimₓ xs finZeroElim]
  exact h

theorem models_sentence_iff (T : L.Theory) (φ : L.Sentence) :
    T ⊨ φ ↔
      ∀ M : Type max u v [Nonempty M] [str : L.Structure M], @Theory.Model L M str T → @RealizeSentence L M str φ :=
  by
  rw [models_formula_iff]
  refine' forall_congrₓ fun M => forall_congrₓ fun ne => forall_congrₓ fun str => _
  refine' ⟨fun h => h Pempty.elimₓ, fun h v => _⟩
  rw [Subsingleton.elimₓ v Pempty.elimₓ]
  exact h

variable {n : ℕ}

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def SemanticallyEquivalent (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ bd_imp φ ψ⊓bd_imp ψ φ

theorem SemanticallyEquivalent.realize_eq {T : L.Theory} {φ ψ : L.BoundedFormula α n} {M : Type max u v}
    [ne : Nonempty M] [str : L.Structure M] (hM : T.Model M) (h : T.SemanticallyEquivalent φ ψ) :
    RealizeBoundedFormulaₓ M φ = RealizeBoundedFormulaₓ M ψ :=
  funext fun v =>
    funext fun xs => by
      have h' := h M v xs hM
      simp only [realize_bounded_formula, has_inf_inf, realize_not, not_forall, exists_prop, not_and, not_not] at h'
      exact iff_eq_eq.mp ⟨h'.1, h'.2⟩

theorem SemanticallyEquivalent.some_model_realize_eq {T : L.Theory} {φ ψ : L.BoundedFormula α n}
    (hsat : T.IsSatisfiable) (h : T.SemanticallyEquivalent φ ψ) :
    RealizeBoundedFormulaₓ hsat.SomeModel φ = RealizeBoundedFormulaₓ hsat.SomeModel ψ :=
  h.realize_eq hsat.some_model_models

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semanticallyEquivalentSetoid (T : L.Theory) : Setoidₓ (L.BoundedFormula α n) where
  R := SemanticallyEquivalent T
  iseqv :=
    ⟨fun φ M ne str v xs hM => by
      simp , fun φ ψ h M ne str v xs hM => by
      have := Ne
      have h := h M v xs hM
      rw [realize_inf, and_comm] at h
      rw [realize_inf]
      exact h, fun φ ψ θ h1 h2 M ne str v xs hM => by
      have := Ne
      have h1' := h1 M v xs hM
      have h2' := h2 M v xs hM
      rw [realize_inf, realize_imp, realize_imp] at *
      exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩⟩

theorem semantically_equivalent_not_not {T : L.Theory} {φ : L.BoundedFormula α n} :
    T.SemanticallyEquivalent φ (bdNot (bdNot φ)) := fun M ne str v xs hM => by
  simp

theorem imp_semantically_equivalent_not_sup {T : L.Theory} {φ ψ : L.BoundedFormula α n} :
    T.SemanticallyEquivalent (bd_imp φ ψ) (bdNot φ⊔ψ) := fun M ne str v xs hM => by
  simp

theorem sup_semantically_equivalent_not_inf_not {T : L.Theory} {φ ψ : L.BoundedFormula α n} :
    T.SemanticallyEquivalent (φ⊔ψ) (bdNot (bdNot φ⊓bdNot ψ)) := fun M ne str v xs hM => by
  simp

theorem inf_semantically_equivalent_not_sup_not {T : L.Theory} {φ ψ : L.BoundedFormula α n} :
    T.SemanticallyEquivalent (φ⊓ψ) (bdNot (bdNot φ⊔bdNot ψ)) := fun M ne str v xs hM => by
  simp only [realize_bounded_formula, has_inf_inf, has_sup_sup, realize_not, not_forall, not_not, exists_prop, and_imp,
    not_and, and_selfₓ]
  exact fun h1 h2 => ⟨h1, h2⟩

end Theory

end Language

end FirstOrder

