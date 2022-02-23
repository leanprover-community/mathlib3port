/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathbin.Data.Equiv.Fin
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


universe u v w u' v'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

variable {M : Type w} {N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'}

open_locale FirstOrder

open Structure

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term (α : Type u') : Type max u u'
  | var {} : ∀ a : α, term
  | func {} : ∀ {l : ℕ} f : L.Functions l ts : Finₓ l → term, term

export Term ()

variable {L}

namespace Term

/-- Relabels a term's variables along a particular function. -/
@[simp]
def relabelₓ (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun i => (ts i).relabel

instance [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩

instance : Coe L.Constants (L.Term α) :=
  ⟨fun c => func c default⟩

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
@[simp]
def realizeₓ (v : α → M) : ∀ t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize

@[simp]
theorem realize_relabel {t : L.Term α} {g : α → β} {v : β → M} : (t.relabel g).realize v = t.realize (v ∘ g) := by
  induction' t with _ n f ts ih
  · rfl
    
  · simp [ih]
    

end Term

@[simp]
theorem Hom.realize_term (g : M →[L] N) {t : L.Term α} {v : α → M} : t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  · rfl
    
  · rw [term.realize, term.realize, g.map_fun]
    refine' congr rfl _
    ext x
    simp [t_ih x]
    

@[simp]
theorem Embedding.realize_term {v : α → M} (t : L.Term α) (g : M ↪[L] N) : t.realize (g ∘ v) = g (t.realize v) :=
  g.toHom.realize_term

@[simp]
theorem Equiv.realize_term {v : α → M} (t : L.Term α) (g : M ≃[L] N) : t.realize (g ∘ v) = g (t.realize v) :=
  g.toHom.realize_term

variable (L) (α)

/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {} {n} : bounded_formula n
  | equal {n} (t₁ t₂ : L.Term (Sum α (Finₓ n))) : bounded_formula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Finₓ l → L.Term (Sum α (Finₓ n))) : bounded_formula n
  | imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
  | all {n} (f : bounded_formula (n + 1)) : bounded_formula n

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible]
def Formula :=
  L.BoundedFormula α 0

/-- A sentence is a formula with no free variables. -/
@[reducible]
def Sentence :=
  L.Formula Empty

/-- A theory is a set of sentences. -/
@[reducible]
def Theory :=
  Set L.Sentence

variable {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {l : ℕ} (R : L.Relations n) (ts : Finₓ n → L.Term (Sum α (Finₓ l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts

/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a bounded formula. -/
def Relations.formula (R : L.Relations n) (ts : Finₓ n → L.Term α) : L.Formula α :=
  R.BoundedFormula fun i => (ts i).relabel Sum.inl

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

namespace BoundedFormula

instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩

instance : HasBot (L.BoundedFormula α n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.Not.all.Not

instance : HasTop (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩

instance : HasInf (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.Not).Not⟩

instance : HasSup (L.BoundedFormula α n) :=
  ⟨fun f g => f.Not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ⊓ψ.imp φ

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → Sum β (Finₓ n)) (k : ℕ) : Sum α (Finₓ k) → Sum β (Finₓ (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equivₓ.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]
theorem sum_elim_comp_relabel_aux {m : ℕ} {g : α → Sum β (Finₓ n)} {v : β → M} {xs : Finₓ (n + m) → M} :
    Sum.elim v xs ∘ relabelAux g m = Sum.elim (Sum.elim v (xs ∘ Finₓ.castAdd m) ∘ g) (xs ∘ Finₓ.natAdd n) := by
  ext x
  cases x
  · simp only [bounded_formula.relabel_aux, Function.comp_app, Sum.map_inl, Sum.elim_inl]
    cases' g x with l r <;> simp
    
  · simp [bounded_formula.relabel_aux]
    

/-- Relabels a bounded formula's variables along a particular function. -/
def relabelₓ (g : α → Sum β (Finₓ n)) : ∀ {k : ℕ}, L.BoundedFormula α k → L.BoundedFormula β (n + k)
  | k, falsum => falsum
  | k, equal t₁ t₂ => (t₁.relabel (relabelAux g k)).bdEqual (t₂.relabel (relabelAux g k))
  | k, rel R ts => R.BoundedFormula (Term.relabelₓ (relabelAux g k) ∘ ts)
  | k, imp f₁ f₂ => f₁.relabel.imp f₂.relabel
  | k, all f => f.relabel.all

/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def allsₓ : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | n + 1, φ => φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exsₓ : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | n + 1, φ => φ.ex.exs

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def Realizeₓ : ∀ {l} f : L.BoundedFormula α l v : α → M xs : Finₓ l → M, Prop
  | _, falsum, v, xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, imp f₁ f₂, v, xs => realize f₁ v xs → realize f₂ v xs
  | _, all f, v, xs => ∀ x : M, realize f v (Finₓ.snoc xs x)

variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}

variable {v : α → M} {xs : Finₓ l → M}

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormula α l).realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_not : φ.Not.realize v xs ↔ ¬φ.realize v xs :=
  Iff.rfl

@[simp]
theorem realize_bd_equal (t₁ t₂ : L.Term (Sum α (Finₓ l))) :
    (t₁.bdEqual t₂).realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormula α l).realize v xs ↔ True := by
  simp [HasTop.top]

@[simp]
theorem realize_inf : (φ⊓ψ).realize v xs ↔ φ.realize v xs ∧ ψ.realize v xs := by
  simp [HasInf.inf, realize]

@[simp]
theorem realize_imp : (φ.imp ψ).realize v xs ↔ φ.realize v xs → ψ.realize v xs := by
  simp only [realize]

@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Finₓ k → L.Term _} :
    (R.BoundedFormula ts).realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_sup : (φ⊔ψ).realize v xs ↔ φ.realize v xs ∨ ψ.realize v xs := by
  simp only [realize, HasSup.sup, realize_not, eq_iff_iff]
  tauto

@[simp]
theorem realize_all : (all θ).realize v xs ↔ ∀ a : M, θ.realize v (Finₓ.snoc xs a) :=
  Iff.rfl

@[simp]
theorem realize_ex : θ.ex.realize v xs ↔ ∃ a : M, θ.realize v (Finₓ.snoc xs a) := by
  rw [bounded_formula.ex, realize_not, realize_all, not_forall]
  simp_rw [realize_not, not_not]

@[simp]
theorem realize_iff : (φ.Iff ψ).realize v xs ↔ (φ.realize v xs ↔ ψ.realize v xs) := by
  simp only [bounded_formula.iff, realize_inf, realize_imp, and_imp, ← iff_def]

theorem realize_relabel {m n : ℕ} {φ : L.BoundedFormula α n} {g : α → Sum β (Finₓ m)} {v : β → M}
    {xs : Finₓ (m + n) → M} :
    (φ.relabel g).realize v xs ↔ φ.realize (Sum.elim v (xs ∘ Finₓ.castAdd n) ∘ g) (xs ∘ Finₓ.natAdd m) := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 n' _ ih3
  · rfl
    
  · simp [realize, relabel]
    
  · simp [realize, relabel]
    
  · simp [realize, relabel, ih1, ih2]
    
  · simp only [ih3, realize, relabel]
    refine'
      forall_congrₓ fun a =>
        iff_eq_eq.mpr (congr (congr rfl (congr (congr rfl (congr rfl (funext fun i => (dif_pos _).trans rfl))) rfl)) _)
    · ext i
      by_cases' h : i.val < n'
      · exact (dif_pos (Nat.add_lt_add_leftₓ h m)).trans (dif_pos h).symm
        
      · exact (dif_neg fun h' => h (Nat.lt_of_add_lt_add_leftₓ h')).trans (dif_neg h).symm
        
      
    

end BoundedFormula

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel

attribute [protected] bounded_formula.imp bounded_formula.all

namespace Formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  BoundedFormula.relabelₓ (Sum.inl ∘ g)

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions n) : L.Formula (Finₓ (n + 1)) :=
  equal (var 0) (func f fun i => var i.succ)

/-- The negation of a formula. -/
protected def not (φ : L.Formula α) : L.Formula α :=
  φ.Not

/-- The implication between formulas, as a formula. -/
protected def imp : L.Formula α → L.Formula α → L.Formula α :=
  bounded_formula.imp

/-- The biimplication between formulas, as a formula. -/
protected def iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.Iff ψ

/-- A formula can be evaluated as true or false by giving values to each free variable. -/
def Realize (φ : L.Formula α) (v : α → M) : Prop :=
  φ.realize v default

variable {M} {φ ψ : L.Formula α} {v : α → M}

@[simp]
theorem realize_not : φ.Not.realize v ↔ ¬φ.realize v :=
  Iff.rfl

@[simp]
theorem realize_bot : (⊥ : L.Formula α).realize v ↔ False :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.Formula α).realize v ↔ True :=
  bounded_formula.realize_top

@[simp]
theorem realize_inf : (φ⊓ψ).realize v ↔ φ.realize v ∧ ψ.realize v :=
  bounded_formula.realize_inf

@[simp]
theorem realize_imp : (φ.imp ψ).realize v ↔ φ.realize v → ψ.realize v :=
  bounded_formula.realize_imp

@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Finₓ k → L.Term α} :
    (R.Formula ts).realize v ↔ RelMap R fun i => (ts i).realize v :=
  BoundedFormula.realize_rel.trans
    (by
      simp )

@[simp]
theorem realize_sup : (φ⊔ψ).realize v ↔ φ.realize v ∨ ψ.realize v :=
  bounded_formula.realize_sup

@[simp]
theorem realize_iff : (φ.Iff ψ).realize v ↔ (φ.realize v ↔ ψ.realize v) :=
  bounded_formula.realize_iff

@[simp]
theorem realize_relabel {φ : L.Formula α} {g : α → β} {v : β → M} : (φ.relabel g).realize v ↔ φ.realize (v ∘ g) := by
  rw [realize, realize, relabel, bounded_formula.realize_relabel, iff_eq_eq]
  refine' congr (congr rfl _) (funext finZeroElim)
  ext
  simp

@[simp]
theorem realize_equal {t₁ t₂ : L.Term α} {x : α → M} : (t₁.equal t₂).realize x ↔ t₁.realize x = t₂.realize x := by
  simp [term.equal, realize]

@[simp]
theorem realize_graph {f : L.Functions n} {x : Finₓ n → M} {y : M} :
    (Formula.graph f).realize (Finₓ.cons y x : _ → M) ↔ funMap f x = y := by
  simp only [formula.graph, term.realize, realize_equal, Finₓ.cons_zero, Finₓ.cons_succ]
  rw [eq_comm]

end Formula

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
@[reducible]
def RealizeSentence (φ : L.Sentence) : Prop :=
  φ.realize (default : _ → M)

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

namespace BoundedFormula

@[simp]
theorem realize_alls {φ : L.BoundedFormula α n} {v : α → M} : φ.alls.realize v ↔ ∀ xs : Finₓ n → M, φ.realize v xs := by
  induction' n with n ih
  · exact unique.forall_iff.symm
    
  · simp only [alls, ih, realize]
    exact ⟨fun h xs => Finₓ.snoc_init_self xs ▸ h _ _, fun h xs x => h (Finₓ.snoc xs x)⟩
    

@[simp]
theorem realize_exs {φ : L.BoundedFormula α n} {v : α → M} : φ.exs.realize v ↔ ∃ xs : Finₓ n → M, φ.realize v xs := by
  induction' n with n ih
  · exact unique.exists_iff.symm
    
  · simp only [bounded_formula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
      
    · rintro ⟨xs, h⟩
      rw [← Finₓ.snoc_init_self xs] at h
      exact ⟨_, _, h⟩
      
    

end BoundedFormula

@[simp]
theorem Equiv.realize_bounded_formula (g : M ≃[L] N) (φ : L.BoundedFormula α n) {v : α → M} {xs : Finₓ n → M} :
    φ.realize (g ∘ v) (g ∘ xs) ↔ φ.realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp only [bounded_formula.realize, ← Sum.comp_elim, equiv.realize_term, g.injective.eq_iff]
    
  · simp only [bounded_formula.realize, ← Sum.comp_elim, equiv.realize_term, g.map_rel]
    
  · rw [bounded_formula.realize, ih1, ih2, bounded_formula.realize]
    
  · rw [bounded_formula.realize, bounded_formula.realize]
    constructor
    · intro h a
      have h' := h (g a)
      rw [← Finₓ.comp_snoc, ih3] at h'
      exact h'
      
    · intro h a
      have h' := h (g.symm a)
      rw [← ih3, Finₓ.comp_snoc, g.apply_symm_apply] at h'
      exact h'
      
    

@[simp]
theorem Equiv.realize_formula (g : M ≃[L] N) (φ : L.Formula α) {v : α → M} : φ.realize (g ∘ v) ↔ φ.realize v := by
  rw [formula.realize, formula.realize, ← g.realize_bounded_formula φ, iff_eq_eq]
  exact congr rfl (funext finZeroElim)

namespace Theory

variable (T : L.Theory)

/-- A theory is satisfiable if a structure models it. -/
def IsSatisfiable : Prop :=
  ∃ (M : Type max u v)(_ : Nonempty M)(str : L.Structure M), @Theory.Model L M str T

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def IsFinitelySatisfiable : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → (T0 : L.Theory).IsSatisfiable

variable {T} {T' : L.Theory}

/-- Given that a theory is satisfiable, selects a model using choice. -/
def IsSatisfiable.SomeModel (h : T.IsSatisfiable) : Type _ :=
  Classical.some h

instance IsSatisfiable.nonempty_some_model (h : T.IsSatisfiable) : Nonempty h.SomeModel :=
  Classical.some (Classical.some_spec h)

noncomputable instance IsSatisfiable.inhabitedSomeModel (h : T.IsSatisfiable) : Inhabited h.SomeModel :=
  Classical.inhabitedOfNonempty'

noncomputable instance IsSatisfiable.someModelStructure (h : T.IsSatisfiable) : L.Structure h.SomeModel :=
  Classical.some (Classical.some_spec (Classical.some_spec h))

theorem IsSatisfiable.some_model_models (h : T.IsSatisfiable) : T.Model h.SomeModel :=
  Classical.some_spec (Classical.some_spec (Classical.some_spec h))

theorem Model.is_satisfiable (M : Type max u v) [n : Nonempty M] [S : L.Structure M] (h : T.Model M) :
    T.IsSatisfiable :=
  ⟨M, n, S, h⟩

theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
  ⟨h.SomeModel, h.nonempty_some_model, h.someModelStructure, h.some_model_models.mono hs⟩

theorem IsSatisfiable.is_finitely_satisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable := fun _ => h.mono

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def ModelsBoundedFormula (T : L.Theory) (φ : L.BoundedFormula α n) : Prop :=
  ∀ M : Type max u v [Nonempty M] [str : L.Structure M] v : α → M xs : Finₓ n → M,
    @Theory.Model L M str T → @BoundedFormula.Realizeₓ L M str α n φ v xs

-- mathport name: «expr ⊨ »
infixl:51 " ⊨ " => ModelsBoundedFormula

-- input using \|= or \vDash, but not using \models
theorem models_formula_iff {T : L.Theory} {φ : L.Formula α} :
    T ⊨ φ ↔
      ∀ M : Type max u v [Nonempty M] [str : L.Structure M] v : α → M,
        @Theory.Model L M str T → @Formula.Realize L M str α φ v :=
  forall_congrₓ fun M => forall_congrₓ fun ne => forall_congrₓ fun str => forall_congrₓ fun v => Unique.forall_iff

theorem models_sentence_iff {T : L.Theory} {φ : L.Sentence} :
    T ⊨ φ ↔
      ∀ M : Type max u v [Nonempty M] [str : L.Structure M], @Theory.Model L M str T → @RealizeSentence L M str φ :=
  by
  rw [models_formula_iff]
  exact forall_congrₓ fun M => forall_congrₓ fun ne => forall_congrₓ fun str => Unique.forall_iff

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def SemanticallyEquivalent (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ φ.Iff ψ

theorem SemanticallyEquivalent.realize_bd_iff {φ ψ : L.BoundedFormula α n} {M : Type max u v} [ne : Nonempty M]
    [str : L.Structure M] (hM : T.Model M) (h : T.SemanticallyEquivalent φ ψ) {v : α → M} {xs : Finₓ n → M} :
    φ.realize v xs ↔ ψ.realize v xs :=
  BoundedFormula.realize_iff.1 (h M v xs hM)

theorem SemanticallyEquivalent.some_model_realize_bd_iff {φ ψ : L.BoundedFormula α n} (hsat : T.IsSatisfiable)
    (h : T.SemanticallyEquivalent φ ψ) {v : α → hsat.SomeModel} {xs : Finₓ n → hsat.SomeModel} :
    φ.realize v xs ↔ ψ.realize v xs :=
  h.realize_bd_iff hsat.some_model_models

theorem SemanticallyEquivalent.realize_iff {φ ψ : L.Formula α} {M : Type max u v} [ne : Nonempty M]
    [str : L.Structure M] (hM : T.Model M) (h : T.SemanticallyEquivalent φ ψ) {v : α → M} : φ.realize v ↔ ψ.realize v :=
  h.realize_bd_iff hM

theorem SemanticallyEquivalent.some_model_realize_iff {φ ψ : L.Formula α} (hsat : T.IsSatisfiable)
    (h : T.SemanticallyEquivalent φ ψ) {v : α → hsat.SomeModel} : φ.realize v ↔ ψ.realize v :=
  h.realize_iff hsat.some_model_models

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semanticallyEquivalentSetoid (T : L.Theory) : Setoidₓ (L.BoundedFormula α n) where
  R := SemanticallyEquivalent T
  iseqv :=
    ⟨fun φ M ne str v xs hM => by
      simp , fun φ ψ h M ne str v xs hM => by
      have := Ne
      rw [bounded_formula.realize_iff, Iff.comm, ← bounded_formula.realize_iff]
      exact h M v xs hM, fun φ ψ θ h1 h2 M ne str v xs hM => by
      have := Ne
      have h1' := h1 M v xs hM
      have h2' := h2 M v xs hM
      rw [bounded_formula.realize_iff] at *
      exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩⟩

end Theory

namespace BoundedFormula

variable {T : L.Theory} (φ ψ : L.BoundedFormula α n)

theorem semantically_equivalent_not_not : T.SemanticallyEquivalent φ φ.Not.Not := fun M ne str v xs hM => by
  simp

theorem imp_semantically_equivalent_not_sup : T.SemanticallyEquivalent (φ.imp ψ) (φ.Not⊔ψ) := fun M ne str v xs hM => by
  simp [imp_iff_not_or]

theorem sup_semantically_equivalent_not_inf_not : T.SemanticallyEquivalent (φ⊔ψ) (φ.Not⊓ψ.Not).Not :=
  fun M ne str v xs hM => by
  simp [imp_iff_not_or]

theorem inf_semantically_equivalent_not_sup_not : T.SemanticallyEquivalent (φ⊓ψ) (φ.Not⊔ψ.Not).Not :=
  fun M ne str v xs hM => by
  simp [and_iff_not_or_not]

end BoundedFormula

namespace Formula

variable {T : L.Theory} (φ ψ : L.Formula α)

theorem semantically_equivalent_not_not : T.SemanticallyEquivalent φ φ.Not.Not :=
  φ.semantically_equivalent_not_not

theorem imp_semantically_equivalent_not_sup : T.SemanticallyEquivalent (φ.imp ψ) (φ.Not⊔ψ) :=
  φ.imp_semantically_equivalent_not_sup ψ

theorem sup_semantically_equivalent_not_inf_not : T.SemanticallyEquivalent (φ⊔ψ) (φ.Not⊓ψ.Not).Not :=
  φ.sup_semantically_equivalent_not_inf_not ψ

theorem inf_semantically_equivalent_not_sup_not : T.SemanticallyEquivalent (φ⊓ψ) (φ.Not⊔ψ.Not).Not :=
  φ.inf_semantically_equivalent_not_sup_not ψ

end Formula

end Language

end FirstOrder

