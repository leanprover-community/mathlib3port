/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Data.List.ProdSigma
import Data.Set.Prod
import Logic.Equiv.Fin
import ModelTheory.LanguageMap

#align_import model_theory.syntax from "leanprover-community/mathlib"@"ce38d86c0b2d427ce208c3cee3159cb421d2b3c4"

/-!
# Basics on First-Order Syntax

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language.term` is defined so that `L.term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `first_order.language.formula` is defined so that `L.formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `first_order.language.sentence` is a formula with no free variables.
* A `first_order.language.Theory` is a set of sentences.
* The variables of terms and formulas can be relabelled with `first_order.language.term.relabel`,
`first_order.language.bounded_formula.relabel`, and `first_order.language.formula.relabel`.
* Given an operation on terms and an operation on relations,
  `first_order.language.bounded_formula.map_term_rel` gives an operation on formulas.
* `first_order.language.bounded_formula.cast_le` adds more `fin`-indexed variables.
* `first_order.language.bounded_formula.lift_at` raises the indexes of the `fin`-indexed variables
above a particular index.
* `first_order.language.term.subst` and `first_order.language.bounded_formula.subst` substitute
variables with given terms.
* Language maps can act on syntactic objects with functions such as
`first_order.language.Lhom.on_formula`.
* `first_order.language.term.constants_vars_equiv` and
`first_order.language.bounded_formula.constants_vars_equiv` switch terms and formulas between having
constants in the language and having extra variables indexed by the same type.

## Implementation Notes
* Formulas use a modified version of de Bruijn variables. Specifically, a `L.bounded_formula α n`
is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
indexed by `fin n`, which can. For any `φ : L.bounded_formula α (n + 1)`, we define the formula
`∀' φ : L.bounded_formula α n` by universally quantifying over the variable indexed by
`n : fin (n + 1)`.

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

variable (L : Language.{u, v}) {L' : Language}

variable {M : Type w} {N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'} {γ : Type _}

open scoped FirstOrder

open Structure Fin

/- ./././Mathport/Syntax/Translate/Command.lean:380:30: infer kinds are unsupported in Lean 4: var {} -/
/- ./././Mathport/Syntax/Translate/Command.lean:380:30: infer kinds are unsupported in Lean 4: func {} -/
#print FirstOrder.Language.Term /-
/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term (α : Type u') : Type max u u'
  | var : ∀ a : α, term
  | func : ∀ {l : ℕ} (f : L.Functions l) (ts : Fin l → term), term
#align first_order.language.term FirstOrder.Language.Term
-/

export Term ()

variable {L}

namespace Term

open Finset

#print FirstOrder.Language.Term.varFinset /-
/-- The `finset` of variables used in a given term. -/
@[simp]
def varFinset [DecidableEq α] : L.term α → Finset α
  | var i => {i}
  | func f ts => univ.biUnion fun i => (ts i).varFinset
#align first_order.language.term.var_finset FirstOrder.Language.Term.varFinset
-/

#print FirstOrder.Language.Term.varFinsetLeft /-
/-- The `finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft [DecidableEq α] : L.term (Sum α β) → Finset α
  | var (Sum.inl i) => {i}
  | var (Sum.inr i) => ∅
  | func f ts => univ.biUnion fun i => (ts i).varFinsetLeft
#align first_order.language.term.var_finset_left FirstOrder.Language.Term.varFinsetLeft
-/

#print FirstOrder.Language.Term.relabel /-
/-- Relabels a term's variables along a particular function. -/
@[simp]
def relabel (g : α → β) : L.term α → L.term β
  | var i => var (g i)
  | func f ts => func f fun i => (ts i).relabel
#align first_order.language.term.relabel FirstOrder.Language.Term.relabel
-/

#print FirstOrder.Language.Term.relabel_id /-
theorem relabel_id (t : L.term α) : t.relabel id = t :=
  by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]
#align first_order.language.term.relabel_id FirstOrder.Language.Term.relabel_id
-/

#print FirstOrder.Language.Term.relabel_id_eq_id /-
@[simp]
theorem relabel_id_eq_id : (Term.relabel id : L.term α → L.term α) = id :=
  funext relabel_id
#align first_order.language.term.relabel_id_eq_id FirstOrder.Language.Term.relabel_id_eq_id
-/

#print FirstOrder.Language.Term.relabel_relabel /-
@[simp]
theorem relabel_relabel (f : α → β) (g : β → γ) (t : L.term α) :
    (t.relabel f).relabel g = t.relabel (g ∘ f) :=
  by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]
#align first_order.language.term.relabel_relabel FirstOrder.Language.Term.relabel_relabel
-/

#print FirstOrder.Language.Term.relabel_comp_relabel /-
@[simp]
theorem relabel_comp_relabel (f : α → β) (g : β → γ) :
    (Term.relabel g ∘ Term.relabel f : L.term α → L.term γ) = Term.relabel (g ∘ f) :=
  funext (relabel_relabel f g)
#align first_order.language.term.relabel_comp_relabel FirstOrder.Language.Term.relabel_comp_relabel
-/

#print FirstOrder.Language.Term.relabelEquiv /-
/-- Relabels a term's variables along a bijection. -/
@[simps]
def relabelEquiv (g : α ≃ β) : L.term α ≃ L.term β :=
  ⟨relabel g, relabel g.symm, fun t => by simp, fun t => by simp⟩
#align first_order.language.term.relabel_equiv FirstOrder.Language.Term.relabelEquiv
-/

#print FirstOrder.Language.Term.restrictVar /-
/-- Restricts a term to use only a set of the given variables. -/
def restrictVar [DecidableEq α] : ∀ (t : L.term α) (f : t.varFinset → β), L.term β
  | var a, f => var (f ⟨a, mem_singleton_self a⟩)
  | func F ts, f =>
    func F fun i => (ts i).restrictVar (f ∘ Set.inclusion (subset_biUnion_of_mem _ (mem_univ i)))
#align first_order.language.term.restrict_var FirstOrder.Language.Term.restrictVar
-/

#print FirstOrder.Language.Term.restrictVarLeft /-
/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeft [DecidableEq α] {γ : Type _} :
    ∀ (t : L.term (Sum α γ)) (f : t.varFinsetLeft → β), L.term (Sum β γ)
  | var (Sum.inl a), f => var (Sum.inl (f ⟨a, mem_singleton_self a⟩))
  | var (Sum.inr a), f => var (Sum.inr a)
  | func F ts, f =>
    func F fun i =>
      (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_biUnion_of_mem _ (mem_univ i)))
#align first_order.language.term.restrict_var_left FirstOrder.Language.Term.restrictVarLeft
-/

end Term

#print FirstOrder.Language.Constants.term /-
/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants) : L.term α :=
  func c default
#align first_order.language.constants.term FirstOrder.Language.Constants.term
-/

#print FirstOrder.Language.Functions.apply₁ /-
/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions 1) (t : L.term α) : L.term α :=
  func f ![t]
#align first_order.language.functions.apply₁ FirstOrder.Language.Functions.apply₁
-/

#print FirstOrder.Language.Functions.apply₂ /-
/-- Applies a binary function to two terms. -/
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.term α) : L.term α :=
  func f ![t₁, t₂]
#align first_order.language.functions.apply₂ FirstOrder.Language.Functions.apply₂
-/

namespace Term

#print FirstOrder.Language.Term.constantsToVars /-
/-- Sends a term with constants to a term with extra variables. -/
@[simp]
def constantsToVars : L[[γ]].term α → L.term (Sum γ α)
  | var a => var (Sum.inr a)
  | @func _ _ 0 f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => var (Sum.inl c)
  | @func _ _ (n + 1) f ts =>
    Sum.casesOn f (fun f => func f fun i => (ts i).constantsToVars) fun c => isEmptyElim c
#align first_order.language.term.constants_to_vars FirstOrder.Language.Term.constantsToVars
-/

#print FirstOrder.Language.Term.varsToConstants /-
/-- Sends a term with extra variables to a term with constants. -/
@[simp]
def varsToConstants : L.term (Sum γ α) → L[[γ]].term α
  | var (Sum.inr a) => var a
  | var (Sum.inl c) => Constants.term (Sum.inr c)
  | func f ts => func (Sum.inl f) fun i => (ts i).varsToConstants
#align first_order.language.term.vars_to_constants FirstOrder.Language.Term.varsToConstants
-/

#print FirstOrder.Language.Term.constantsVarsEquiv /-
/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
def constantsVarsEquiv : L[[γ]].term α ≃ L.term (Sum γ α) :=
  ⟨constantsToVars, varsToConstants, by
    intro t
    induction' t with _ n f _ ih
    · rfl
    · cases n
      · cases f
        · simp [constants_to_vars, vars_to_constants, ih]
        · simp [constants_to_vars, vars_to_constants, constants.term]
      · cases f
        · simp [constants_to_vars, vars_to_constants, ih]
        · exact isEmptyElim f, by
    intro t
    induction' t with x n f _ ih
    · cases x <;> rfl
    · cases n <;> · simp [vars_to_constants, constants_to_vars, ih]⟩
#align first_order.language.term.constants_vars_equiv FirstOrder.Language.Term.constantsVarsEquiv
-/

#print FirstOrder.Language.Term.constantsVarsEquivLeft /-
/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquivLeft : L[[γ]].term (Sum α β) ≃ L.term (Sum (Sum γ α) β) :=
  constantsVarsEquiv.trans (relabelEquiv (Equiv.sumAssoc _ _ _)).symm
#align first_order.language.term.constants_vars_equiv_left FirstOrder.Language.Term.constantsVarsEquivLeft
-/

#print FirstOrder.Language.Term.constantsVarsEquivLeft_apply /-
@[simp]
theorem constantsVarsEquivLeft_apply (t : L[[γ]].term (Sum α β)) :
    constantsVarsEquivLeft t = (constantsToVars t).relabel (Equiv.sumAssoc _ _ _).symm :=
  rfl
#align first_order.language.term.constants_vars_equiv_left_apply FirstOrder.Language.Term.constantsVarsEquivLeft_apply
-/

#print FirstOrder.Language.Term.constantsVarsEquivLeft_symm_apply /-
@[simp]
theorem constantsVarsEquivLeft_symm_apply (t : L.term (Sum (Sum γ α) β)) :
    constantsVarsEquivLeft.symm t = varsToConstants (t.relabel (Equiv.sumAssoc _ _ _)) :=
  rfl
#align first_order.language.term.constants_vars_equiv_left_symm_apply FirstOrder.Language.Term.constantsVarsEquivLeft_symm_apply
-/

#print FirstOrder.Language.Term.inhabitedOfVar /-
instance inhabitedOfVar [Inhabited α] : Inhabited (L.term α) :=
  ⟨var default⟩
#align first_order.language.term.inhabited_of_var FirstOrder.Language.Term.inhabitedOfVar
-/

#print FirstOrder.Language.Term.inhabitedOfConstant /-
instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.term α) :=
  ⟨(default : L.Constants).term⟩
#align first_order.language.term.inhabited_of_constant FirstOrder.Language.Term.inhabitedOfConstant
-/

#print FirstOrder.Language.Term.liftAt /-
/-- Raises all of the `fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def liftAt {n : ℕ} (n' m : ℕ) : L.term (Sum α (Fin n)) → L.term (Sum α (Fin (n + n'))) :=
  relabel (Sum.map id fun i => if ↑i < m then Fin.castAddEmb n' i else Fin.addNatEmb n' i)
#align first_order.language.term.lift_at FirstOrder.Language.Term.liftAt
-/

#print FirstOrder.Language.Term.subst /-
/-- Substitutes the variables in a given term with terms. -/
@[simp]
def subst : L.term α → (α → L.term β) → L.term β
  | var a, tf => tf a
  | func f ts, tf => func f fun i => (ts i).subst tf
#align first_order.language.term.subst FirstOrder.Language.Term.subst
-/

end Term

scoped[FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

namespace Lhom

/- warning: first_order.language.Lhom.on_term clashes with first_order.language.LHom.on_term -> FirstOrder.Language.LHom.onTerm
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.on_term FirstOrder.Language.LHom.onTermₓ'. -/
#print FirstOrder.Language.LHom.onTerm /-
/-- Maps a term's symbols along a language map. -/
@[simp]
def onTerm (φ : L →ᴸ L') : L.term α → L'.term α
  | var i => var i
  | func f ts => func (φ.onFunction f) fun i => on_term (ts i)
#align first_order.language.Lhom.on_term FirstOrder.Language.LHom.onTerm
-/

/- warning: first_order.language.Lhom.id_on_term clashes with first_order.language.LHom.id_on_term -> FirstOrder.Language.LHom.id_onTerm
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.id_on_term FirstOrder.Language.LHom.id_onTermₓ'. -/
#print FirstOrder.Language.LHom.id_onTerm /-
@[simp]
theorem id_onTerm : ((LHom.id L).onTerm : L.term α → L.term α) = id :=
  by
  ext t
  induction' t with _ _ _ _ ih
  · rfl
  · simp_rw [on_term, ih]
    rfl
#align first_order.language.Lhom.id_on_term FirstOrder.Language.LHom.id_onTerm
-/

/- warning: first_order.language.Lhom.comp_on_term clashes with first_order.language.LHom.comp_on_term -> FirstOrder.Language.LHom.comp_onTerm
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.comp_on_term FirstOrder.Language.LHom.comp_onTermₓ'. -/
#print FirstOrder.Language.LHom.comp_onTerm /-
@[simp]
theorem comp_onTerm {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.term α → L''.term α) = φ.onTerm ∘ ψ.onTerm :=
  by
  ext t
  induction' t with _ _ _ _ ih
  · rfl
  · simp_rw [on_term, ih]
    rfl
#align first_order.language.Lhom.comp_on_term FirstOrder.Language.LHom.comp_onTerm
-/

end Lhom

#print FirstOrder.Language.Lequiv.onTerm /-
/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def Lequiv.onTerm (φ : L ≃ᴸ L') : L.term α ≃ L'.term α
    where
  toFun := φ.toLhom.onTerm
  invFun := φ.invLhom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← Lhom.comp_on_term, φ.left_inv, Lhom.id_on_term]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← Lhom.comp_on_term, φ.right_inv, Lhom.id_on_term]
#align first_order.language.Lequiv.on_term FirstOrder.Language.Lequiv.onTerm
-/

variable (L) (α)

/- ./././Mathport/Syntax/Translate/Command.lean:380:30: infer kinds are unsupported in Lean 4: falsum {} -/
#print FirstOrder.Language.BoundedFormula /-
/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive BoundedFormula : ℕ → Type max u v u'
  | falsum {n} : bounded_formula n
  | equal {n} (t₁ t₂ : L.term (Sum α (Fin n))) : bounded_formula n
  | Rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.term (Sum α (Fin n))) : bounded_formula n
  | imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
  | all {n} (f : bounded_formula (n + 1)) : bounded_formula n
#align first_order.language.bounded_formula FirstOrder.Language.BoundedFormula
-/

#print FirstOrder.Language.Formula /-
/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible]
def Formula :=
  L.BoundedFormula α 0
#align first_order.language.formula FirstOrder.Language.Formula
-/

#print FirstOrder.Language.Sentence /-
/-- A sentence is a formula with no free variables. -/
@[reducible]
def Sentence :=
  L.Formula Empty
#align first_order.language.sentence FirstOrder.Language.Sentence
-/

#print FirstOrder.Language.Theory /-
/-- A theory is a set of sentences. -/
@[reducible]
def Theory :=
  Set L.Sentence
#align first_order.language.Theory FirstOrder.Language.Theory
-/

variable {L} {α} {n : ℕ}

#print FirstOrder.Language.Relations.boundedFormula /-
/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {l : ℕ} (R : L.Relations n) (ts : Fin n → L.term (Sum α (Fin l))) :
    L.BoundedFormula α l :=
  BoundedFormula.rel R ts
#align first_order.language.relations.bounded_formula FirstOrder.Language.Relations.boundedFormula
-/

#print FirstOrder.Language.Relations.boundedFormula₁ /-
/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.term (Sum α (Fin n))) :
    L.BoundedFormula α n :=
  r.BoundedFormula ![t]
#align first_order.language.relations.bounded_formula₁ FirstOrder.Language.Relations.boundedFormula₁
-/

#print FirstOrder.Language.Relations.boundedFormula₂ /-
/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.term (Sum α (Fin n))) :
    L.BoundedFormula α n :=
  r.BoundedFormula ![t₁, t₂]
#align first_order.language.relations.bounded_formula₂ FirstOrder.Language.Relations.boundedFormula₂
-/

#print FirstOrder.Language.Term.bdEqual /-
/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.term (Sum α (Fin n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂
#align first_order.language.term.bd_equal FirstOrder.Language.Term.bdEqual
-/

#print FirstOrder.Language.Relations.formula /-
/-- Applies a relation to terms as a bounded formula. -/
def Relations.formula (R : L.Relations n) (ts : Fin n → L.term α) : L.Formula α :=
  R.BoundedFormula fun i => (ts i).relabel Sum.inl
#align first_order.language.relations.formula FirstOrder.Language.Relations.formula
-/

#print FirstOrder.Language.Relations.formula₁ /-
/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations 1) (t : L.term α) : L.Formula α :=
  r.Formula ![t]
#align first_order.language.relations.formula₁ FirstOrder.Language.Relations.formula₁
-/

#print FirstOrder.Language.Relations.formula₂ /-
/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.term α) : L.Formula α :=
  r.Formula ![t₁, t₂]
#align first_order.language.relations.formula₂ FirstOrder.Language.Relations.formula₂
-/

#print FirstOrder.Language.Term.equal /-
/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)
#align first_order.language.term.equal FirstOrder.Language.Term.equal
-/

namespace BoundedFormula

instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩

instance : Bot (L.BoundedFormula α n) :=
  ⟨falsum⟩

#print FirstOrder.Language.BoundedFormula.not /-
/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥
#align first_order.language.bounded_formula.not FirstOrder.Language.BoundedFormula.not
-/

#print FirstOrder.Language.BoundedFormula.ex /-
/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
protected def ex (φ : L.BoundedFormula α (n + 1)) : L.BoundedFormula α n :=
  φ.Not.all.Not
#align first_order.language.bounded_formula.ex FirstOrder.Language.BoundedFormula.ex
-/

instance : Top (L.BoundedFormula α n) :=
  ⟨BoundedFormula.not ⊥⟩

instance : Inf (L.BoundedFormula α n) :=
  ⟨fun f g => (f.imp g.Not).Not⟩

instance : Sup (L.BoundedFormula α n) :=
  ⟨fun f g => f.Not.imp g⟩

#print FirstOrder.Language.BoundedFormula.iff /-
/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α n) :=
  φ.imp ψ ⊓ ψ.imp φ
#align first_order.language.bounded_formula.iff FirstOrder.Language.BoundedFormula.iff
-/

open Finset

#print FirstOrder.Language.BoundedFormula.freeVarFinset /-
/-- The `finset` of variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq α] : ∀ {n}, L.BoundedFormula α n → Finset α
  | n, falsum => ∅
  | n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | n, Rel R ts => univ.biUnion fun i => (ts i).varFinsetLeft
  | n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | n, all f => f.freeVarFinset
#align first_order.language.bounded_formula.free_var_finset FirstOrder.Language.BoundedFormula.freeVarFinset
-/

#print FirstOrder.Language.BoundedFormula.castLE /-
/-- Casts `L.bounded_formula α m` as `L.bounded_formula α n`, where `m ≤ n`. -/
@[simp]
def castLE : ∀ {m n : ℕ} (h : m ≤ n), L.BoundedFormula α m → L.BoundedFormula α n
  | m, n, h, falsum => falsum
  | m, n, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLEEmb h))) (t₂.relabel (Sum.map id (Fin.castLEEmb h)))
  | m, n, h, Rel R ts => rel R (Term.relabel (Sum.map id (Fin.castLEEmb h)) ∘ ts)
  | m, n, h, imp f₁ f₂ => (f₁.castLEEmb h).imp (f₂.castLEEmb h)
  | m, n, h, all f => (f.castLEEmb (add_le_add_right h 1)).all
#align first_order.language.bounded_formula.cast_le FirstOrder.Language.BoundedFormula.castLE
-/

#print FirstOrder.Language.BoundedFormula.castLE_rfl /-
@[simp]
theorem castLE_rfl {n} (h : n ≤ n) (φ : L.BoundedFormula α n) : φ.castLEEmb h = φ :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [Fin.castLE_of_eq]
  · simp [Fin.castLE_of_eq]
  · simp [Fin.castLE_of_eq, ih1, ih2]
  · simp [Fin.castLE_of_eq, ih3]
#align first_order.language.bounded_formula.cast_le_rfl FirstOrder.Language.BoundedFormula.castLE_rfl
-/

#print FirstOrder.Language.BoundedFormula.castLE_castLE /-
@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.BoundedFormula α k) :
    (φ.castLEEmb km).castLEEmb mn = φ.castLEEmb (km.trans mn) :=
  by
  revert m n
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3 <;> intro m n km mn
  · rfl
  · simp
  · simp only [cast_le, eq_self_iff_true, heq_iff_eq, true_and_iff]
    rw [← Function.comp.assoc, relabel_comp_relabel]
    simp
  · simp [ih1, ih2]
  · simp only [cast_le, ih3]
#align first_order.language.bounded_formula.cast_le_cast_le FirstOrder.Language.BoundedFormula.castLE_castLE
-/

#print FirstOrder.Language.BoundedFormula.castLE_comp_castLE /-
@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    (BoundedFormula.castLE mn ∘ BoundedFormula.castLE km :
        L.BoundedFormula α k → L.BoundedFormula α n) =
      BoundedFormula.castLE (km.trans mn) :=
  funext (castLE_castLE km mn)
#align first_order.language.bounded_formula.cast_le_comp_cast_le FirstOrder.Language.BoundedFormula.castLE_comp_castLE
-/

#print FirstOrder.Language.BoundedFormula.restrictFreeVar /-
/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrictFreeVar [DecidableEq α] :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (f : φ.freeVarFinset → β), L.BoundedFormula β n
  | n, falsum, f => falsum
  | n, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (f ∘ Set.inclusion (subset_union_left _ _)))
      (t₂.restrictVarLeft (f ∘ Set.inclusion (subset_union_right _ _)))
  | n, Rel R ts, f =>
    rel R fun i => (ts i).restrictVarLeft (f ∘ Set.inclusion (subset_biUnion_of_mem _ (mem_univ i)))
  | n, imp φ₁ φ₂, f =>
    (φ₁.restrictFreeVar (f ∘ Set.inclusion (subset_union_left _ _))).imp
      (φ₂.restrictFreeVar (f ∘ Set.inclusion (subset_union_right _ _)))
  | n, all φ, f => (φ.restrictFreeVar f).all
#align first_order.language.bounded_formula.restrict_free_var FirstOrder.Language.BoundedFormula.restrictFreeVar
-/

#print FirstOrder.Language.BoundedFormula.alls /-
/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | n + 1, φ => φ.all.alls
#align first_order.language.bounded_formula.alls FirstOrder.Language.BoundedFormula.alls
-/

#print FirstOrder.Language.BoundedFormula.exs /-
/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {n}, L.BoundedFormula α n → L.Formula α
  | 0, φ => φ
  | n + 1, φ => φ.ex.exs
#align first_order.language.bounded_formula.exs FirstOrder.Language.BoundedFormula.exs
-/

#print FirstOrder.Language.BoundedFormula.mapTermRel /-
/-- Maps bounded formulas along a map of terms and a map of relations. -/
def mapTermRel {g : ℕ → ℕ} (ft : ∀ n, L.term (Sum α (Fin n)) → L'.term (Sum β (Fin (g n))))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)) :
    ∀ {n}, L.BoundedFormula α n → L'.BoundedFormula β (g n)
  | n, falsum => falsum
  | n, equal t₁ t₂ => equal (ft _ t₁) (ft _ t₂)
  | n, Rel R ts => rel (fr _ R) fun i => ft _ (ts i)
  | n, imp φ₁ φ₂ => φ₁.mapTermRel.imp φ₂.mapTermRel
  | n, all φ => (h n φ.mapTermRel).all
#align first_order.language.bounded_formula.map_term_rel FirstOrder.Language.BoundedFormula.mapTermRel
-/

#print FirstOrder.Language.BoundedFormula.liftAt /-
/-- Raises all of the `fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def liftAt : ∀ {n : ℕ} (n' m : ℕ), L.BoundedFormula α n → L.BoundedFormula α (n + n') :=
  fun n n' m φ =>
  φ.mapTermRel (fun k t => t.liftAt n' m) (fun _ => id) fun _ =>
    castLE (by rw [add_assoc, add_comm 1, add_assoc])
#align first_order.language.bounded_formula.lift_at FirstOrder.Language.BoundedFormula.liftAt
-/

#print FirstOrder.Language.BoundedFormula.mapTermRel_mapTermRel /-
@[simp]
theorem mapTermRel_mapTermRel {L'' : Language}
    (ft : ∀ n, L.term (Sum α (Fin n)) → L'.term (Sum β (Fin n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (ft' : ∀ n, L'.term (Sum β (Fin n)) → L''.term (Sum γ (Fin n)))
    (fr' : ∀ n, L'.Relations n → L''.Relations n) {n} (φ : L.BoundedFormula α n) :
    ((φ.mapTermRel ft fr fun _ => id).mapTermRel ft' fr' fun _ => id) =
      φ.mapTermRel (fun _ => ft' _ ∘ ft _) (fun _ => fr' _ ∘ fr _) fun _ => id :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [map_term_rel]
  · simp [map_term_rel]
  · simp [map_term_rel, ih1, ih2]
  · simp [map_term_rel, ih3]
#align first_order.language.bounded_formula.map_term_rel_map_term_rel FirstOrder.Language.BoundedFormula.mapTermRel_mapTermRel
-/

#print FirstOrder.Language.BoundedFormula.mapTermRel_id_id_id /-
@[simp]
theorem mapTermRel_id_id_id {n} (φ : L.BoundedFormula α n) :
    (φ.mapTermRel (fun _ => id) (fun _ => id) fun _ => id) = φ :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [map_term_rel]
  · simp [map_term_rel]
  · simp [map_term_rel, ih1, ih2]
  · simp [map_term_rel, ih3]
#align first_order.language.bounded_formula.map_term_rel_id_id_id FirstOrder.Language.BoundedFormula.mapTermRel_id_id_id
-/

#print FirstOrder.Language.BoundedFormula.mapTermRelEquiv /-
/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps]
def mapTermRelEquiv (ft : ∀ n, L.term (Sum α (Fin n)) ≃ L'.term (Sum β (Fin n)))
    (fr : ∀ n, L.Relations n ≃ L'.Relations n) {n} : L.BoundedFormula α n ≃ L'.BoundedFormula β n :=
  ⟨mapTermRel (fun n => ft n) (fun n => fr n) fun _ => id,
    mapTermRel (fun n => (ft n).symm) (fun n => (fr n).symm) fun _ => id, fun φ => by simp, fun φ =>
    by simp⟩
#align first_order.language.bounded_formula.map_term_rel_equiv FirstOrder.Language.BoundedFormula.mapTermRelEquiv
-/

#print FirstOrder.Language.BoundedFormula.relabelAux /-
/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → Sum β (Fin n)) (k : ℕ) : Sum α (Fin k) → Sum β (Fin (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id
#align first_order.language.bounded_formula.relabel_aux FirstOrder.Language.BoundedFormula.relabelAux
-/

#print FirstOrder.Language.BoundedFormula.sum_elim_comp_relabelAux /-
@[simp]
theorem sum_elim_comp_relabelAux {m : ℕ} {g : α → Sum β (Fin n)} {v : β → M}
    {xs : Fin (n + m) → M} :
    Sum.elim v xs ∘ relabelAux g m =
      Sum.elim (Sum.elim v (xs ∘ castAddEmb m) ∘ g) (xs ∘ natAddEmb n) :=
  by
  ext x
  cases x
  · simp only [bounded_formula.relabel_aux, Function.comp_apply, Sum.map_inl, Sum.elim_inl]
    cases' g x with l r <;> simp
  · simp [bounded_formula.relabel_aux]
#align first_order.language.bounded_formula.sum_elim_comp_relabel_aux FirstOrder.Language.BoundedFormula.sum_elim_comp_relabelAux
-/

#print FirstOrder.Language.BoundedFormula.relabelAux_sum_inl /-
@[simp]
theorem relabelAux_sum_inl (k : ℕ) :
    relabelAux (Sum.inl : α → Sum α (Fin n)) k = Sum.map id (natAddEmb n) :=
  by
  ext x
  cases x <;> · simp [relabel_aux]
#align first_order.language.bounded_formula.relabel_aux_sum_inl FirstOrder.Language.BoundedFormula.relabelAux_sum_inl
-/

#print FirstOrder.Language.BoundedFormula.relabel /-
/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → Sum β (Fin n)) {k} (φ : L.BoundedFormula α k) : L.BoundedFormula β (n + k) :=
  φ.mapTermRel (fun _ t => t.relabel (relabelAux g _)) (fun _ => id) fun _ =>
    castLE (ge_of_eq (add_assoc _ _ _))
#align first_order.language.bounded_formula.relabel FirstOrder.Language.BoundedFormula.relabel
-/

#print FirstOrder.Language.BoundedFormula.relabelEquiv /-
/-- Relabels a bounded formula's free variables along a bijection. -/
def relabelEquiv (g : α ≃ β) {k} : L.BoundedFormula α k ≃ L.BoundedFormula β k :=
  mapTermRelEquiv (fun n => Term.relabelEquiv (g.sumCongr (Equiv.refl _))) fun n => Equiv.refl _
#align first_order.language.bounded_formula.relabel_equiv FirstOrder.Language.BoundedFormula.relabelEquiv
-/

#print FirstOrder.Language.BoundedFormula.relabel_falsum /-
@[simp]
theorem relabel_falsum (g : α → Sum β (Fin n)) {k} :
    (falsum : L.BoundedFormula α k).relabel g = falsum :=
  rfl
#align first_order.language.bounded_formula.relabel_falsum FirstOrder.Language.BoundedFormula.relabel_falsum
-/

#print FirstOrder.Language.BoundedFormula.relabel_bot /-
@[simp]
theorem relabel_bot (g : α → Sum β (Fin n)) {k} : (⊥ : L.BoundedFormula α k).relabel g = ⊥ :=
  rfl
#align first_order.language.bounded_formula.relabel_bot FirstOrder.Language.BoundedFormula.relabel_bot
-/

#print FirstOrder.Language.BoundedFormula.relabel_imp /-
@[simp]
theorem relabel_imp (g : α → Sum β (Fin n)) {k} (φ ψ : L.BoundedFormula α k) :
    (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
  rfl
#align first_order.language.bounded_formula.relabel_imp FirstOrder.Language.BoundedFormula.relabel_imp
-/

#print FirstOrder.Language.BoundedFormula.relabel_not /-
@[simp]
theorem relabel_not (g : α → Sum β (Fin n)) {k} (φ : L.BoundedFormula α k) :
    φ.Not.relabel g = (φ.relabel g).Not := by simp [bounded_formula.not]
#align first_order.language.bounded_formula.relabel_not FirstOrder.Language.BoundedFormula.relabel_not
-/

#print FirstOrder.Language.BoundedFormula.relabel_all /-
@[simp]
theorem relabel_all (g : α → Sum β (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.all.relabel g = (φ.relabel g).all :=
  by
  rw [relabel, map_term_rel, relabel]
  simp
#align first_order.language.bounded_formula.relabel_all FirstOrder.Language.BoundedFormula.relabel_all
-/

#print FirstOrder.Language.BoundedFormula.relabel_ex /-
@[simp]
theorem relabel_ex (g : α → Sum β (Fin n)) {k} (φ : L.BoundedFormula α (k + 1)) :
    φ.ex.relabel g = (φ.relabel g).ex := by simp [bounded_formula.ex]
#align first_order.language.bounded_formula.relabel_ex FirstOrder.Language.BoundedFormula.relabel_ex
-/

#print FirstOrder.Language.BoundedFormula.relabel_sum_inl /-
@[simp]
theorem relabel_sum_inl (φ : L.BoundedFormula α n) :
    (φ.relabel Sum.inl : L.BoundedFormula α (0 + n)) = φ.castLEEmb (ge_of_eq (zero_add n)) :=
  by
  simp only [relabel, relabel_aux_sum_inl]
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [Fin.natAdd_zero, cast_le_of_eq, map_term_rel]
  · simp [Fin.natAdd_zero, cast_le_of_eq, map_term_rel]
  · simp [map_term_rel, ih1, ih2]
  · simp [map_term_rel, ih3, cast_le]
#align first_order.language.bounded_formula.relabel_sum_inl FirstOrder.Language.BoundedFormula.relabel_sum_inl
-/

#print FirstOrder.Language.BoundedFormula.subst /-
/-- Substitutes the variables in a given formula with terms. -/
@[simp]
def subst {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.term β) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ t => t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)))
    (fun _ => id) fun _ => id
#align first_order.language.bounded_formula.subst FirstOrder.Language.BoundedFormula.subst
-/

#print FirstOrder.Language.BoundedFormula.constantsVarsEquiv /-
/-- A bijection sending formulas with constants to formulas with extra variables. -/
def constantsVarsEquiv : L[[γ]].BoundedFormula α n ≃ L.BoundedFormula (Sum γ α) n :=
  mapTermRelEquiv (fun _ => Term.constantsVarsEquivLeft) fun _ => Equiv.sumEmpty _ _
#align first_order.language.bounded_formula.constants_vars_equiv FirstOrder.Language.BoundedFormula.constantsVarsEquiv
-/

#print FirstOrder.Language.BoundedFormula.toFormula /-
/-- Turns the extra variables of a bounded formula into free variables. -/
@[simp]
def toFormula : ∀ {n : ℕ}, L.BoundedFormula α n → L.Formula (Sum α (Fin n))
  | n, falsum => falsum
  | n, equal t₁ t₂ => t₁.equal t₂
  | n, Rel R ts => R.Formula ts
  | n, imp φ₁ φ₂ => φ₁.toFormula.imp φ₂.toFormula
  | n, all φ =>
    (φ.toFormula.relabel
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))).all
#align first_order.language.bounded_formula.to_formula FirstOrder.Language.BoundedFormula.toFormula
-/

variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}

variable {v : α → M} {xs : Fin l → M}

#print FirstOrder.Language.BoundedFormula.IsAtomic /-
/-- An atomic formula is either equality or a relation symbol applied to terms.
  Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive IsAtomic : L.BoundedFormula α n → Prop
  | equal (t₁ t₂ : L.term (Sum α (Fin n))) : IsAtomic (bdEqual t₁ t₂)
  |
  Rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.term (Sum α (Fin n))) :
    IsAtomic (R.BoundedFormula ts)
#align first_order.language.bounded_formula.is_atomic FirstOrder.Language.BoundedFormula.IsAtomic
-/

#print FirstOrder.Language.BoundedFormula.not_all_isAtomic /-
theorem not_all_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic := fun con => by
  cases Con
#align first_order.language.bounded_formula.not_all_is_atomic FirstOrder.Language.BoundedFormula.not_all_isAtomic
-/

#print FirstOrder.Language.BoundedFormula.not_ex_isAtomic /-
theorem not_ex_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic := fun con => by cases Con
#align first_order.language.bounded_formula.not_ex_is_atomic FirstOrder.Language.BoundedFormula.not_ex_isAtomic
-/

#print FirstOrder.Language.BoundedFormula.IsAtomic.relabel /-
theorem IsAtomic.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsAtomic)
    (f : α → Sum β (Fin n)) : (φ.relabel f).IsAtomic :=
  IsAtomic.rec_on h (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _
#align first_order.language.bounded_formula.is_atomic.relabel FirstOrder.Language.BoundedFormula.IsAtomic.relabel
-/

#print FirstOrder.Language.BoundedFormula.IsAtomic.liftAt /-
theorem IsAtomic.liftAt {k m : ℕ} (h : IsAtomic φ) : (φ.liftAt k m).IsAtomic :=
  IsAtomic.rec_on h (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _
#align first_order.language.bounded_formula.is_atomic.lift_at FirstOrder.Language.BoundedFormula.IsAtomic.liftAt
-/

#print FirstOrder.Language.BoundedFormula.IsAtomic.castLE /-
theorem IsAtomic.castLE {h : l ≤ n} (hφ : IsAtomic φ) : (φ.castLEEmb h).IsAtomic :=
  IsAtomic.rec_on hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _
#align first_order.language.bounded_formula.is_atomic.cast_le FirstOrder.Language.BoundedFormula.IsAtomic.castLE
-/

#print FirstOrder.Language.BoundedFormula.IsQF /-
/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive IsQF : L.BoundedFormula α n → Prop
  | falsum : is_qf falsum
  | of_is_atomic {φ} (h : IsAtomic φ) : is_qf φ
  | imp {φ₁ φ₂} (h₁ : is_qf φ₁) (h₂ : is_qf φ₂) : is_qf (φ₁.imp φ₂)
#align first_order.language.bounded_formula.is_qf FirstOrder.Language.BoundedFormula.IsQF
-/

#print FirstOrder.Language.BoundedFormula.IsAtomic.isQF /-
theorem IsAtomic.isQF {φ : L.BoundedFormula α n} : IsAtomic φ → IsQF φ :=
  IsQF.of_isAtomic
#align first_order.language.bounded_formula.is_atomic.is_qf FirstOrder.Language.BoundedFormula.IsAtomic.isQF
-/

#print FirstOrder.Language.BoundedFormula.isQF_bot /-
theorem isQF_bot : IsQF (⊥ : L.BoundedFormula α n) :=
  IsQF.falsum
#align first_order.language.bounded_formula.is_qf_bot FirstOrder.Language.BoundedFormula.isQF_bot
-/

#print FirstOrder.Language.BoundedFormula.IsQF.not /-
theorem IsQF.not {φ : L.BoundedFormula α n} (h : IsQF φ) : IsQF φ.Not :=
  h.imp isQF_bot
#align first_order.language.bounded_formula.is_qf.not FirstOrder.Language.BoundedFormula.IsQF.not
-/

#print FirstOrder.Language.BoundedFormula.IsQF.relabel /-
theorem IsQF.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsQF) (f : α → Sum β (Fin n)) :
    (φ.relabel f).IsQF :=
  IsQF.rec_on h isQF_bot (fun _ h => (h.relabel f).IsQF) fun _ _ _ _ h1 h2 => h1.imp h2
#align first_order.language.bounded_formula.is_qf.relabel FirstOrder.Language.BoundedFormula.IsQF.relabel
-/

#print FirstOrder.Language.BoundedFormula.IsQF.liftAt /-
theorem IsQF.liftAt {k m : ℕ} (h : IsQF φ) : (φ.liftAt k m).IsQF :=
  IsQF.rec_on h isQF_bot (fun _ ih => ih.liftAt.IsQF) fun _ _ _ _ ih1 ih2 => ih1.imp ih2
#align first_order.language.bounded_formula.is_qf.lift_at FirstOrder.Language.BoundedFormula.IsQF.liftAt
-/

#print FirstOrder.Language.BoundedFormula.IsQF.castLE /-
theorem IsQF.castLE {h : l ≤ n} (hφ : IsQF φ) : (φ.castLEEmb h).IsQF :=
  IsQF.rec_on hφ isQF_bot (fun _ ih => ih.castLEEmb.IsQF) fun _ _ _ _ ih1 ih2 => ih1.imp ih2
#align first_order.language.bounded_formula.is_qf.cast_le FirstOrder.Language.BoundedFormula.IsQF.castLE
-/

#print FirstOrder.Language.BoundedFormula.not_all_isQF /-
theorem not_all_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQF := fun con =>
  by
  cases' Con with _ con
  exact φ.not_all_is_atomic Con
#align first_order.language.bounded_formula.not_all_is_qf FirstOrder.Language.BoundedFormula.not_all_isQF
-/

#print FirstOrder.Language.BoundedFormula.not_ex_isQF /-
theorem not_ex_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQF := fun con =>
  by
  cases' Con with _ con _ _ con
  · exact φ.not_ex_is_atomic Con
  · exact not_all_is_qf _ Con
#align first_order.language.bounded_formula.not_ex_is_qf FirstOrder.Language.BoundedFormula.not_ex_isQF
-/

#print FirstOrder.Language.BoundedFormula.IsPrenex /-
/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive IsPrenex : ∀ {n}, L.BoundedFormula α n → Prop
  | of_is_qf {n} {φ : L.BoundedFormula α n} (h : IsQF φ) : is_prenex φ
  | all {n} {φ : L.BoundedFormula α (n + 1)} (h : is_prenex φ) : is_prenex φ.all
  | ex {n} {φ : L.BoundedFormula α (n + 1)} (h : is_prenex φ) : is_prenex φ.ex
#align first_order.language.bounded_formula.is_prenex FirstOrder.Language.BoundedFormula.IsPrenex
-/

#print FirstOrder.Language.BoundedFormula.IsQF.isPrenex /-
theorem IsQF.isPrenex {φ : L.BoundedFormula α n} : IsQF φ → IsPrenex φ :=
  IsPrenex.of_isQF
#align first_order.language.bounded_formula.is_qf.is_prenex FirstOrder.Language.BoundedFormula.IsQF.isPrenex
-/

#print FirstOrder.Language.BoundedFormula.IsAtomic.isPrenex /-
theorem IsAtomic.isPrenex {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsPrenex φ :=
  h.IsQF.IsPrenex
#align first_order.language.bounded_formula.is_atomic.is_prenex FirstOrder.Language.BoundedFormula.IsAtomic.isPrenex
-/

#print FirstOrder.Language.BoundedFormula.IsPrenex.induction_on_all_not /-
theorem IsPrenex.induction_on_all_not {P : ∀ {n}, L.BoundedFormula α n → Prop}
    {φ : L.BoundedFormula α n} (h : IsPrenex φ)
    (hq : ∀ {m} {ψ : L.BoundedFormula α m}, ψ.IsQF → P ψ)
    (ha : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hn : ∀ {m} {ψ : L.BoundedFormula α m}, P ψ → P ψ.Not) : P φ :=
  IsPrenex.rec_on h (fun _ _ => hq) (fun _ _ _ => ha) fun _ _ _ ih => hn (ha (hn ih))
#align first_order.language.bounded_formula.is_prenex.induction_on_all_not FirstOrder.Language.BoundedFormula.IsPrenex.induction_on_all_not
-/

#print FirstOrder.Language.BoundedFormula.IsPrenex.relabel /-
theorem IsPrenex.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsPrenex)
    (f : α → Sum β (Fin n)) : (φ.relabel f).IsPrenex :=
  IsPrenex.rec_on h (fun _ _ h => (h.relabel f).IsPrenex) (fun _ _ _ h => by simp [h.all])
    fun _ _ _ h => by simp [h.ex]
#align first_order.language.bounded_formula.is_prenex.relabel FirstOrder.Language.BoundedFormula.IsPrenex.relabel
-/

#print FirstOrder.Language.BoundedFormula.IsPrenex.castLE /-
theorem IsPrenex.castLE (hφ : IsPrenex φ) : ∀ {n} {h : l ≤ n}, (φ.castLEEmb h).IsPrenex :=
  IsPrenex.rec_on hφ (fun _ _ ih _ _ => ih.castLEEmb.IsPrenex) (fun _ _ _ ih _ _ => ih.all)
    fun _ _ _ ih _ _ => ih.ex
#align first_order.language.bounded_formula.is_prenex.cast_le FirstOrder.Language.BoundedFormula.IsPrenex.castLE
-/

#print FirstOrder.Language.BoundedFormula.IsPrenex.liftAt /-
theorem IsPrenex.liftAt {k m : ℕ} (h : IsPrenex φ) : (φ.liftAt k m).IsPrenex :=
  IsPrenex.rec_on h (fun _ _ ih => ih.liftAt.IsPrenex) (fun _ _ _ ih => ih.castLEEmb.all)
    fun _ _ _ ih => ih.castLEEmb.ex
#align first_order.language.bounded_formula.is_prenex.lift_at FirstOrder.Language.BoundedFormula.IsPrenex.liftAt
-/

#print FirstOrder.Language.BoundedFormula.toPrenexImpRight /-
/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.to_prenex_imp_right ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImpRight : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, φ, bounded_formula.ex ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).ex
  | n, φ, all ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).all
  | n, φ, ψ => φ.imp ψ
#align first_order.language.bounded_formula.to_prenex_imp_right FirstOrder.Language.BoundedFormula.toPrenexImpRight
-/

#print FirstOrder.Language.BoundedFormula.IsQF.toPrenexImpRight /-
theorem IsQF.toPrenexImpRight {φ : L.BoundedFormula α n} :
    ∀ {ψ : L.BoundedFormula α n}, IsQF ψ → φ.toPrenexImpRight ψ = φ.imp ψ
  | _, is_qf.falsum => rfl
  | _, is_qf.of_is_atomic (is_atomic.equal _ _) => rfl
  | _, is_qf.of_is_atomic (is_atomic.rel _ _) => rfl
  | _, is_qf.imp is_qf.falsum _ => rfl
  | _, is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _ => rfl
  | _, is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _ => rfl
  | _, is_qf.imp (is_qf.imp _ _) _ => rfl
#align first_order.language.bounded_formula.is_qf.to_prenex_imp_right FirstOrder.Language.BoundedFormula.IsQF.toPrenexImpRight
-/

#print FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImpRight /-
theorem isPrenex_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImpRight ψ) :=
  by
  induction' hψ with _ _ hψ _ _ _ ih1 _ _ _ ih2
  · rw [hψ.to_prenex_imp_right]
    exact (hφ.imp hψ).IsPrenex
  · exact (ih1 hφ.lift_at).all
  · exact (ih2 hφ.lift_at).ex
#align first_order.language.bounded_formula.is_prenex_to_prenex_imp_right FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImpRight
-/

#print FirstOrder.Language.BoundedFormula.toPrenexImp /-
/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.to_prenex_imp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImp : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, bounded_formula.ex φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).all
  | n, all φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).ex
  | _, φ, ψ => φ.toPrenexImpRight ψ
#align first_order.language.bounded_formula.to_prenex_imp FirstOrder.Language.BoundedFormula.toPrenexImp
-/

#print FirstOrder.Language.BoundedFormula.IsQF.toPrenexImp /-
theorem IsQF.toPrenexImp :
    ∀ {φ ψ : L.BoundedFormula α n}, φ.IsQF → φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
  | _, _, is_qf.falsum => rfl
  | _, _, is_qf.of_is_atomic (is_atomic.equal _ _) => rfl
  | _, _, is_qf.of_is_atomic (is_atomic.rel _ _) => rfl
  | _, _, is_qf.imp is_qf.falsum _ => rfl
  | _, _, is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _ => rfl
  | _, _, is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _ => rfl
  | _, _, is_qf.imp (is_qf.imp _ _) _ => rfl
#align first_order.language.bounded_formula.is_qf.to_prenex_imp FirstOrder.Language.BoundedFormula.IsQF.toPrenexImp
-/

#print FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImp /-
theorem isPrenex_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImp ψ) :=
  by
  induction' hφ with _ _ hφ _ _ _ ih1 _ _ _ ih2
  · rw [hφ.to_prenex_imp]
    exact is_prenex_to_prenex_imp_right hφ hψ
  · exact (ih1 hψ.lift_at).ex
  · exact (ih2 hψ.lift_at).all
#align first_order.language.bounded_formula.is_prenex_to_prenex_imp FirstOrder.Language.BoundedFormula.isPrenex_toPrenexImp
-/

#print FirstOrder.Language.BoundedFormula.toPrenex /-
/-- For any bounded formula `φ`, `φ.to_prenex` is a semantically-equivalent formula in prenex normal
  form. -/
def toPrenex : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, falsum => ⊥
  | _, equal t₁ t₂ => t₁.bdEqual t₂
  | _, Rel R ts => rel R ts
  | _, imp f₁ f₂ => f₁.toPrenex.toPrenexImp f₂.toPrenex
  | _, all f => f.toPrenex.all
#align first_order.language.bounded_formula.to_prenex FirstOrder.Language.BoundedFormula.toPrenex
-/

#print FirstOrder.Language.BoundedFormula.toPrenex_isPrenex /-
theorem toPrenex_isPrenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  BoundedFormula.recOn φ (fun _ => isQF_bot.IsPrenex) (fun _ _ _ => (IsAtomic.equal _ _).IsPrenex)
    (fun _ _ _ _ => (IsAtomic.rel _ _).IsPrenex) (fun _ _ _ h1 h2 => isPrenex_toPrenexImp h1 h2)
    fun _ _ => IsPrenex.all
#align first_order.language.bounded_formula.to_prenex_is_prenex FirstOrder.Language.BoundedFormula.toPrenex_isPrenex
-/

end BoundedFormula

namespace Lhom

open BoundedFormula

#print FirstOrder.Language.LHom.onBoundedFormula /-
/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
def onBoundedFormula (g : L →ᴸ L') : ∀ {k : ℕ}, L.BoundedFormula α k → L'.BoundedFormula α k
  | k, falsum => falsum
  | k, equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | k, Rel R ts => (g.onRelation R).BoundedFormula (g.onTerm ∘ ts)
  | k, imp f₁ f₂ => (on_bounded_formula f₁).imp (on_bounded_formula f₂)
  | k, all f => (on_bounded_formula f).all
#align first_order.language.Lhom.on_bounded_formula FirstOrder.Language.LHom.onBoundedFormula
-/

#print FirstOrder.Language.LHom.id_onBoundedFormula /-
@[simp]
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α n → L.BoundedFormula α n) = id :=
  by
  ext f
  induction' f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · rw [on_bounded_formula, Lhom.id_on_term, id.def, id.def, id.def, bd_equal]
  · rw [on_bounded_formula, Lhom.id_on_term]
    rfl
  · rw [on_bounded_formula, ih1, ih2, id.def, id.def, id.def]
  · rw [on_bounded_formula, ih3, id.def, id.def]
#align first_order.language.Lhom.id_on_bounded_formula FirstOrder.Language.LHom.id_onBoundedFormula
-/

#print FirstOrder.Language.LHom.comp_onBoundedFormula /-
@[simp]
theorem comp_onBoundedFormula {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α n → L''.BoundedFormula α n) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula :=
  by
  ext f
  induction' f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp only [on_bounded_formula, comp_on_term, Function.comp_apply]
    rfl
  · simp only [on_bounded_formula, comp_on_relation, comp_on_term, Function.comp_apply]
    rfl
  · simp only [on_bounded_formula, Function.comp_apply, ih1, ih2, eq_self_iff_true, and_self_iff]
  · simp only [ih3, on_bounded_formula, Function.comp_apply]
#align first_order.language.Lhom.comp_on_bounded_formula FirstOrder.Language.LHom.comp_onBoundedFormula
-/

#print FirstOrder.Language.LHom.onFormula /-
/-- Maps a formula's symbols along a language map. -/
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula
#align first_order.language.Lhom.on_formula FirstOrder.Language.LHom.onFormula
-/

#print FirstOrder.Language.LHom.onSentence /-
/-- Maps a sentence's symbols along a language map. -/
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula
#align first_order.language.Lhom.on_sentence FirstOrder.Language.LHom.onSentence
-/

#print FirstOrder.Language.LHom.onTheory /-
/-- Maps a theory's symbols along a language map. -/
def onTheory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T
#align first_order.language.Lhom.on_Theory FirstOrder.Language.LHom.onTheory
-/

#print FirstOrder.Language.LHom.mem_onTheory /-
@[simp]
theorem mem_onTheory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ ∈ g.onTheory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _
#align first_order.language.Lhom.mem_on_Theory FirstOrder.Language.LHom.mem_onTheory
-/

end Lhom

namespace Lequiv

#print FirstOrder.Language.LEquiv.onBoundedFormula /-
/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula α n
    where
  toFun := φ.toLhom.onBoundedFormula
  invFun := φ.invLhom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.left_inv,
      Lhom.id_on_bounded_formula]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.right_inv,
      Lhom.id_on_bounded_formula]
#align first_order.language.Lequiv.on_bounded_formula FirstOrder.Language.LEquiv.onBoundedFormula
-/

#print FirstOrder.Language.LEquiv.onBoundedFormula_symm /-
theorem onBoundedFormula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α n ≃ L.BoundedFormula α n) =
      φ.symm.onBoundedFormula :=
  rfl
#align first_order.language.Lequiv.on_bounded_formula_symm FirstOrder.Language.LEquiv.onBoundedFormula_symm
-/

#print FirstOrder.Language.LEquiv.onFormula /-
/-- Maps a formula's symbols along a language equivalence. -/
def onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α :=
  φ.onBoundedFormula
#align first_order.language.Lequiv.on_formula FirstOrder.Language.LEquiv.onFormula
-/

#print FirstOrder.Language.LEquiv.onFormula_apply /-
@[simp]
theorem onFormula_apply (φ : L ≃ᴸ L') :
    (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLhom.onFormula :=
  rfl
#align first_order.language.Lequiv.on_formula_apply FirstOrder.Language.LEquiv.onFormula_apply
-/

#print FirstOrder.Language.LEquiv.onFormula_symm /-
@[simp]
theorem onFormula_symm (φ : L ≃ᴸ L') :
    (φ.onFormula.symm : L'.Formula α ≃ L.Formula α) = φ.symm.onFormula :=
  rfl
#align first_order.language.Lequiv.on_formula_symm FirstOrder.Language.LEquiv.onFormula_symm
-/

#print FirstOrder.Language.LEquiv.onSentence /-
/-- Maps a sentence's symbols along a language equivalence. -/
@[simps]
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula
#align first_order.language.Lequiv.on_sentence FirstOrder.Language.LEquiv.onSentence
-/

end Lequiv

scoped[FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual

-- input \~- or \simeq
scoped[FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp

-- input \==>
scoped[FirstOrder] prefix:110 "∀'" => FirstOrder.Language.BoundedFormula.all

scoped[FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not

-- input \~, the ASCII character ~ has too low precedence
scoped[FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff

-- input \<=>
scoped[FirstOrder] prefix:110 "∃'" => FirstOrder.Language.BoundedFormula.ex

-- input \ex
namespace Formula

#print FirstOrder.Language.Formula.relabel /-
/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0
#align first_order.language.formula.relabel FirstOrder.Language.Formula.relabel
-/

#print FirstOrder.Language.Formula.graph /-
/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  equal (var 0) (func f fun i => var i.succ)
#align first_order.language.formula.graph FirstOrder.Language.Formula.graph
-/

#print FirstOrder.Language.Formula.not /-
/-- The negation of a formula. -/
protected def not (φ : L.Formula α) : L.Formula α :=
  φ.Not
#align first_order.language.formula.not FirstOrder.Language.Formula.not
-/

#print FirstOrder.Language.Formula.imp /-
/-- The implication between formulas, as a formula. -/
protected def imp : L.Formula α → L.Formula α → L.Formula α :=
  BoundedFormula.imp
#align first_order.language.formula.imp FirstOrder.Language.Formula.imp
-/

#print FirstOrder.Language.Formula.iff /-
/-- The biimplication between formulas, as a formula. -/
protected def iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.Iff ψ
#align first_order.language.formula.iff FirstOrder.Language.Formula.iff
-/

#print FirstOrder.Language.Formula.isAtomic_graph /-
theorem isAtomic_graph (f : L.Functions n) : (graph f).IsAtomic :=
  BoundedFormula.IsAtomic.equal _ _
#align first_order.language.formula.is_atomic_graph FirstOrder.Language.Formula.isAtomic_graph
-/

#print FirstOrder.Language.Formula.equivSentence /-
/-- A bijection sending formulas to sentences with constants. -/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans (BoundedFormula.relabelEquiv (Equiv.sumEmpty _ _))).symm
#align first_order.language.formula.equiv_sentence FirstOrder.Language.Formula.equivSentence
-/

#print FirstOrder.Language.Formula.equivSentence_not /-
theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.Not = (equivSentence φ).Not :=
  rfl
#align first_order.language.formula.equiv_sentence_not FirstOrder.Language.Formula.equivSentence_not
-/

#print FirstOrder.Language.Formula.equivSentence_inf /-
theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  rfl
#align first_order.language.formula.equiv_sentence_inf FirstOrder.Language.Formula.equivSentence_inf
-/

end Formula

namespace Relations

variable (r : L.Relations 2)

#print FirstOrder.Language.Relations.reflexive /-
/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.Sentence :=
  ∀'r.boundedFormula₂ (&0) &0
#align first_order.language.relations.reflexive FirstOrder.Language.Relations.reflexive
-/

#print FirstOrder.Language.Relations.irreflexive /-
/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.Sentence :=
  ∀'∼(r.boundedFormula₂ (&0) &0)
#align first_order.language.relations.irreflexive FirstOrder.Language.Relations.irreflexive
-/

#print FirstOrder.Language.Relations.symmetric /-
/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)
#align first_order.language.relations.symmetric FirstOrder.Language.Relations.symmetric
-/

#print FirstOrder.Language.Relations.antisymmetric /-
/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)
#align first_order.language.relations.antisymmetric FirstOrder.Language.Relations.antisymmetric
-/

#print FirstOrder.Language.Relations.transitive /-
/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.Sentence :=
  ∀'∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)
#align first_order.language.relations.transitive FirstOrder.Language.Relations.transitive
-/

#print FirstOrder.Language.Relations.total /-
/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⊔ r.boundedFormula₂ (&1) &0)
#align first_order.language.relations.total FirstOrder.Language.Relations.total
-/

end Relations

section Cardinality

variable (L)

#print FirstOrder.Language.Sentence.cardGe /-
/-- A sentence indicating that a structure has `n` distinct elements. -/
protected def Sentence.cardGe (n) : L.Sentence :=
  (((((List.finRange n).product (List.finRange n)).filterₓ fun ij : _ × _ => ij.1 ≠ ij.2).map
          fun ij : _ × _ => ∼((&ij.1).bdEqual &ij.2)).foldr
      (· ⊓ ·) ⊤).exs
#align first_order.language.sentence.card_ge FirstOrder.Language.Sentence.cardGe
-/

#print FirstOrder.Language.infiniteTheory /-
/-- A theory indicating that a structure is infinite. -/
def infiniteTheory : L.Theory :=
  Set.range (Sentence.cardGe L)
#align first_order.language.infinite_theory FirstOrder.Language.infiniteTheory
-/

#print FirstOrder.Language.nonemptyTheory /-
/-- A theory that indicates a structure is nonempty. -/
def nonemptyTheory : L.Theory :=
  {Sentence.cardGe L 1}
#align first_order.language.nonempty_theory FirstOrder.Language.nonemptyTheory
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.distinctConstantsTheory /-
/-- A theory indicating that each of a set of constants is distinct. -/
def distinctConstantsTheory (s : Set α) : L[[α]].Theory :=
  (fun ab : α × α => ((L.con ab.1).term.equal (L.con ab.2).term).Not) '' (s ×ˢ s ∩ Set.diagonal αᶜ)
#align first_order.language.distinct_constants_theory FirstOrder.Language.distinctConstantsTheory
-/

variable {L} {α}

open Set

#print FirstOrder.Language.monotone_distinctConstantsTheory /-
theorem monotone_distinctConstantsTheory :
    Monotone (L.distinctConstantsTheory : Set α → L[[α]].Theory) := fun s t st =>
  image_subset _ (inter_subset_inter_left _ (prod_mono st st))
#align first_order.language.monotone_distinct_constants_theory FirstOrder.Language.monotone_distinctConstantsTheory
-/

#print FirstOrder.Language.directed_distinctConstantsTheory /-
theorem directed_distinctConstantsTheory :
    Directed (· ⊆ ·) (L.distinctConstantsTheory : Set α → L[[α]].Theory) :=
  Monotone.directed_le monotone_distinctConstantsTheory
#align first_order.language.directed_distinct_constants_theory FirstOrder.Language.directed_distinctConstantsTheory
-/

#print FirstOrder.Language.distinctConstantsTheory_eq_iUnion /-
theorem distinctConstantsTheory_eq_iUnion (s : Set α) :
    L.distinctConstantsTheory s =
      ⋃ t : Finset s,
        L.distinctConstantsTheory (t.map (Function.Embedding.subtype fun x => x ∈ s)) :=
  by
  classical
  simp only [distinct_constants_theory]
  rw [← image_Union, ← Union_inter]
  refine' congr rfl (congr (congr rfl _) rfl)
  ext ⟨i, j⟩
  simp only [prod_mk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_Union,
    mem_image, Finset.mem_coe, Subtype.exists, Subtype.coe_mk, exists_and_right, exists_eq_right]
  refine' ⟨fun h => ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, _⟩, ⟨h.2, _⟩⟩, _⟩
  · simp
  · simp
  · rintro ⟨t, ⟨is, _⟩, ⟨js, _⟩⟩
    exact ⟨is, js⟩
#align first_order.language.distinct_constants_theory_eq_Union FirstOrder.Language.distinctConstantsTheory_eq_iUnion
-/

end Cardinality

end Language

end FirstOrder

