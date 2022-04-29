/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathbin.Logic.Equiv.Fin
import Mathbin.ModelTheory.LanguageMap

/-!
# Basics on First-Order Syntax
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
* `first_order.language.bounded_formula.cast_le` adds more `fin`-indexed variables.
* `first_order.language.bounded_formula.lift_at` raises the indexes of the `fin`-indexed variables
above a particular index.
* Language maps can act on syntactic objects with functions such as
`first_order.language.Lhom.on_formula`.

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

variable {α : Type u'} {β : Type v'}

open FirstOrder

open Structure Finₓ

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive Term (α : Type u') : Type max u u'
  | var {} : ∀ a : α, term
  | func {} : ∀ {l : ℕ} f : L.Functions l ts : Finₓ l → term, term

export Term ()

variable {L}

namespace Term

open List

/-- Relabels a term's variables along a particular function. -/
@[simp]
def relabelₓ (g : α → β) : L.Term α → L.Term β
  | var i => var (g i)
  | func f ts => func f fun i => (ts i).relabel

instance inhabitedOfVar [Inhabited α] : Inhabited (L.Term α) :=
  ⟨var default⟩

end Term

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants) : L.Term α :=
  func c default

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions 1) (t : L.Term α) : L.Term α :=
  func f ![t]

/-- Applies a binary function to two terms. -/
def Functions.apply₂ (f : L.Functions 2) (t₁ t₂ : L.Term α) : L.Term α :=
  func f ![t₁, t₂]

namespace Term

instance inhabitedOfConstant [Inhabited L.Constants] : Inhabited (L.Term α) :=
  ⟨(default : L.Constants).Term⟩

/-- Raises all of the `fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def liftAt {n : ℕ} (n' m : ℕ) : L.Term (Sum α (Finₓ n)) → L.Term (Sum α (Finₓ (n + n'))) :=
  relabelₓ (Sum.map id fun i => if ↑i < m then Finₓ.castAdd n' i else Finₓ.addNat n' i)

end Term

-- mathport name: «expr& »
localized [FirstOrder] prefix:arg "&" => FirstOrder.Language.Term.var ∘ Sum.inr

namespace Lhom

/-- Maps a term's symbols along a language map. -/
@[simp]
def onTermₓ (φ : L →ᴸ L') : L.Term α → L'.Term α
  | var i => var i
  | func f ts => func (φ.onFunction f) fun i => on_term (ts i)

@[simp]
theorem id_on_term : ((Lhom.id L).onTerm : L.Term α → L.Term α) = id := by
  ext t
  induction' t with _ _ _ _ ih
  · rfl
    
  · simp_rw [on_term, ih]
    rfl
    

@[simp]
theorem comp_on_term {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α → L''.Term α) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction' t with _ _ _ _ ih
  · rfl
    
  · simp_rw [on_term, ih]
    rfl
    

end Lhom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def Lequiv.onTerm (φ : L ≃ᴸ L') : L.Term α ≃ L'.Term α where
  toFun := φ.toLhom.onTerm
  invFun := φ.invLhom.onTerm
  left_inv := by
    rw [Function.left_inverse_iff_comp, ← Lhom.comp_on_term, φ.left_inv, Lhom.id_on_term]
  right_inv := by
    rw [Function.right_inverse_iff_comp, ← Lhom.comp_on_term, φ.right_inv, Lhom.id_on_term]

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

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations 1) (t : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  r.BoundedFormula ![t]

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations 2) (t₁ t₂ : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  r.BoundedFormula ![t₁, t₂]

/-- The equality of two terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (Sum α (Finₓ n))) : L.BoundedFormula α n :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a bounded formula. -/
def Relations.formula (R : L.Relations n) (ts : Finₓ n → L.Term α) : L.Formula α :=
  R.BoundedFormula fun i => (ts i).relabel Sum.inl

/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations 1) (t : L.Term α) : L.Formula α :=
  r.Formula ![t]

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations 2) (t₁ t₂ : L.Term α) : L.Formula α :=
  r.Formula ![t₁, t₂]

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α) : L.Formula α :=
  (t₁.relabel Sum.inl).bdEqual (t₂.relabel Sum.inl)

namespace BoundedFormula

instance : Inhabited (L.BoundedFormula α n) :=
  ⟨falsum⟩

instance : HasBot (L.BoundedFormula α n) :=
  ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[matchPattern]
protected def not (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[matchPattern]
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

/-- Casts `L.bounded_formula α m` as `L.bounded_formula α n`, where `m ≤ n`. -/
def castLeₓ : ∀ {m n : ℕ} h : m ≤ n, L.BoundedFormula α m → L.BoundedFormula α n
  | m, n, h, falsum => falsum
  | m, n, h, equal t₁ t₂ => (t₁.relabel (Sum.map id (Finₓ.castLe h))).bdEqual (t₂.relabel (Sum.map id (Finₓ.castLe h)))
  | m, n, h, rel R ts => R.BoundedFormula (Term.relabelₓ (Sum.map id (Finₓ.castLe h)) ∘ ts)
  | m, n, h, imp f₁ f₂ => (f₁.cast_le h).imp (f₂.cast_le h)
  | m, n, h, all f => (f.cast_le (add_le_add_right h 1)).all

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → Sum β (Finₓ n)) (k : ℕ) : Sum α (Finₓ k) → Sum β (Finₓ (n + k)) :=
  Sum.map id finSumFinEquiv ∘ Equivₓ.sumAssoc _ _ _ ∘ Sum.map g id

@[simp]
theorem sum_elim_comp_relabel_aux {m : ℕ} {g : α → Sum β (Finₓ n)} {v : β → M} {xs : Finₓ (n + m) → M} :
    Sum.elim v xs ∘ relabelAux g m = Sum.elim (Sum.elim v (xs ∘ castAdd m) ∘ g) (xs ∘ natAdd n) := by
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

/-- Raises all of the `fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def liftAtₓ : ∀ {n : ℕ} n' m : ℕ, L.BoundedFormula α n → L.BoundedFormula α (n + n')
  | n, n', m, falsum => falsum
  | n, n', m, equal t₁ t₂ => (t₁.liftAt n' m).bdEqual (t₂.liftAt n' m)
  | n, n', m, rel R ts => R.BoundedFormula (Term.liftAt n' m ∘ ts)
  | n, n', m, imp f₁ f₂ => (f₁.liftAt n' m).imp (f₂.liftAt n' m)
  | n, n', m, all f =>
    ((f.liftAt n' m).cast_le
        (by
          rw [add_assocₓ, add_commₓ 1, ← add_assocₓ])).all

variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}

variable {v : α → M} {xs : Finₓ l → M}

/-- An atomic formula is either equality or a relation symbol applied to terms.
  Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive IsAtomic : L.BoundedFormula α n → Prop
  | equal (t₁ t₂ : L.Term (Sum α (Finₓ n))) : is_atomic (bdEqual t₁ t₂)
  | rel {l : ℕ} (R : L.Relations l) (ts : Finₓ l → L.Term (Sum α (Finₓ n))) : is_atomic (R.BoundedFormula ts)

theorem not_all_is_atomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic := fun con => by
  cases con

theorem not_ex_is_atomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic := fun con => by
  cases con

theorem IsAtomic.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsAtomic) (f : α → Sum β (Finₓ n)) :
    (φ.relabel f).IsAtomic :=
  IsAtomic.rec_on h (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _

theorem IsAtomic.lift_at {k m : ℕ} (h : IsAtomic φ) : (φ.liftAt k m).IsAtomic :=
  IsAtomic.rec_on h (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _

theorem IsAtomic.cast_le {h : l ≤ n} (hφ : IsAtomic φ) : (φ.cast_le h).IsAtomic :=
  IsAtomic.rec_on hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ _ => IsAtomic.rel _ _

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive IsQf : L.BoundedFormula α n → Prop
  | falsum : is_qf falsum
  | of_is_atomic {φ} (h : IsAtomic φ) : is_qf φ
  | imp {φ₁ φ₂} (h₁ : is_qf φ₁) (h₂ : is_qf φ₂) : is_qf (φ₁.imp φ₂)

theorem IsAtomic.is_qf {φ : L.BoundedFormula α n} : IsAtomic φ → IsQf φ :=
  is_qf.of_is_atomic

theorem is_qf_bot : IsQf (⊥ : L.BoundedFormula α n) :=
  is_qf.falsum

theorem IsQf.not {φ : L.BoundedFormula α n} (h : IsQf φ) : IsQf φ.Not :=
  h.imp is_qf_bot

theorem IsQf.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsQf) (f : α → Sum β (Finₓ n)) : (φ.relabel f).IsQf :=
  IsQf.rec_on h is_qf_bot (fun _ h => (h.relabel f).IsQf) fun _ _ _ _ h1 h2 => h1.imp h2

theorem IsQf.lift_at {k m : ℕ} (h : IsQf φ) : (φ.liftAt k m).IsQf :=
  IsQf.rec_on h is_qf_bot (fun _ ih => ih.liftAt.IsQf) fun _ _ _ _ ih1 ih2 => ih1.imp ih2

theorem IsQf.cast_le {h : l ≤ n} (hφ : IsQf φ) : (φ.cast_le h).IsQf :=
  IsQf.rec_on hφ is_qf_bot (fun _ ih => ih.cast_le.IsQf) fun _ _ _ _ ih1 ih2 => ih1.imp ih2

theorem not_all_is_qf (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQf := fun con => by
  cases' con with _ con
  exact φ.not_all_is_atomic con

theorem not_ex_is_qf (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQf := fun con => by
  cases' con with _ con _ _ con
  · exact φ.not_ex_is_atomic con
    
  · exact not_all_is_qf _ con
    

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive IsPrenex : ∀ {n}, L.BoundedFormula α n → Prop
  | of_is_qf {n} {φ : L.BoundedFormula α n} (h : IsQf φ) : is_prenex φ
  | all {n} {φ : L.BoundedFormula α (n + 1)} (h : is_prenex φ) : is_prenex φ.all
  | ex {n} {φ : L.BoundedFormula α (n + 1)} (h : is_prenex φ) : is_prenex φ.ex

theorem IsQf.is_prenex {φ : L.BoundedFormula α n} : IsQf φ → IsPrenex φ :=
  is_prenex.of_is_qf

theorem IsAtomic.is_prenex {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsPrenex φ :=
  h.IsQf.IsPrenex

theorem IsPrenex.induction_on_all_not {P : ∀ {n}, L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : IsPrenex φ) (hq : ∀ {m} {ψ : L.BoundedFormula α m}, ψ.IsQf → P ψ)
    (ha : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hn : ∀ {m} {ψ : L.BoundedFormula α m}, P ψ → P ψ.Not) : P φ :=
  IsPrenex.rec_on h (fun _ _ => hq) (fun _ _ _ => ha) fun _ _ _ ih => hn (ha (hn ih))

theorem IsPrenex.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsPrenex) (f : α → Sum β (Finₓ n)) :
    (φ.relabel f).IsPrenex :=
  IsPrenex.rec_on h (fun _ _ h => (h.relabel f).IsPrenex) (fun _ _ _ h => h.all) fun _ _ _ h => h.ex

theorem IsPrenex.cast_le (hφ : IsPrenex φ) : ∀ {n} {h : l ≤ n}, (φ.cast_le h).IsPrenex :=
  IsPrenex.rec_on hφ (fun _ _ ih _ _ => ih.cast_le.IsPrenex) (fun _ _ _ ih _ _ => ih.all) fun _ _ _ ih _ _ => ih.ex

theorem IsPrenex.lift_at {k m : ℕ} (h : IsPrenex φ) : (φ.liftAt k m).IsPrenex :=
  IsPrenex.rec_on h (fun _ _ ih => ih.liftAt.IsPrenex) (fun _ _ _ ih => ih.cast_le.all) fun _ _ _ ih => ih.cast_le.ex

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.to_prenex_imp_right ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImpRightₓ : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, φ, bounded_formula.ex ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).ex
  | n, φ, all ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).all
  | n, φ, ψ => φ.imp ψ

theorem IsQf.to_prenex_imp_right {φ : L.BoundedFormula α n} :
    ∀ {ψ : L.BoundedFormula α n}, IsQf ψ → φ.toPrenexImpRight ψ = φ.imp ψ
  | _, is_qf.falsum => rfl
  | _, is_qf.of_is_atomic (is_atomic.equal _ _) => rfl
  | _, is_qf.of_is_atomic (is_atomic.rel _ _) => rfl
  | _, is_qf.imp is_qf.falsum _ => rfl
  | _, is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _ => rfl
  | _, is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _ => rfl
  | _, is_qf.imp (is_qf.imp _ _) _ => rfl

theorem is_prenex_to_prenex_imp_right {φ ψ : L.BoundedFormula α n} (hφ : IsQf φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImpRight ψ) := by
  induction' hψ with _ _ hψ _ _ _ ih1 _ _ _ ih2
  · rw [hψ.to_prenex_imp_right]
    exact (hφ.imp hψ).IsPrenex
    
  · exact (ih1 hφ.lift_at).all
    
  · exact (ih2 hφ.lift_at).ex
    

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.to_prenex_imp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImpₓ : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, bounded_formula.ex φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).all
  | n, all φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).ex
  | _, φ, ψ => φ.toPrenexImpRight ψ

theorem IsQf.to_prenex_imp : ∀ {φ ψ : L.BoundedFormula α n}, φ.IsQf → φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
  | _, _, is_qf.falsum => rfl
  | _, _, is_qf.of_is_atomic (is_atomic.equal _ _) => rfl
  | _, _, is_qf.of_is_atomic (is_atomic.rel _ _) => rfl
  | _, _, is_qf.imp is_qf.falsum _ => rfl
  | _, _, is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _ => rfl
  | _, _, is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _ => rfl
  | _, _, is_qf.imp (is_qf.imp _ _) _ => rfl

theorem is_prenex_to_prenex_imp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImp ψ) := by
  induction' hφ with _ _ hφ _ _ _ ih1 _ _ _ ih2
  · rw [hφ.to_prenex_imp]
    exact is_prenex_to_prenex_imp_right hφ hψ
    
  · exact (ih1 hψ.lift_at).ex
    
  · exact (ih2 hψ.lift_at).all
    

/-- For any bounded formula `φ`, `φ.to_prenex` is a semantically-equivalent formula in prenex normal
  form. -/
def toPrenexₓ : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, falsum => ⊥
  | _, equal t₁ t₂ => t₁.bdEqual t₂
  | _, rel R ts => rel R ts
  | _, imp f₁ f₂ => f₁.toPrenex.toPrenexImp f₂.toPrenex
  | _, all f => f.toPrenex.all

theorem to_prenex_is_prenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  BoundedFormula.recOn φ (fun _ => is_qf_bot.IsPrenex) (fun _ _ _ => (IsAtomic.equal _ _).IsPrenex)
    (fun _ _ _ _ => (IsAtomic.rel _ _).IsPrenex) (fun _ _ _ h1 h2 => is_prenex_to_prenex_imp h1 h2) fun _ _ =>
    IsPrenex.all

end BoundedFormula

namespace Lhom

open BoundedFormula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
def onBoundedFormulaₓ (g : L →ᴸ L') : ∀ {k : ℕ}, L.BoundedFormula α k → L'.BoundedFormula α k
  | k, falsum => falsum
  | k, equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | k, rel R ts => (g.onRelation R).BoundedFormula (g.onTerm ∘ ts)
  | k, imp f₁ f₂ => (on_bounded_formula f₁).imp (on_bounded_formula f₂)
  | k, all f => (on_bounded_formula f).all

@[simp]
theorem id_on_bounded_formula : ((Lhom.id L).onBoundedFormula : L.BoundedFormula α n → L.BoundedFormula α n) = id := by
  ext f
  induction' f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · rw [on_bounded_formula, Lhom.id_on_term, id.def, id.def, id.def, bd_equal]
    
  · rw [on_bounded_formula, Lhom.id_on_term]
    rfl
    
  · rw [on_bounded_formula, ih1, ih2, id.def, id.def, id.def]
    
  · rw [on_bounded_formula, ih3, id.def, id.def]
    

@[simp]
theorem comp_on_bounded_formula {L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α n → L''.BoundedFormula α n) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula :=
  by
  ext f
  induction' f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp only [on_bounded_formula, comp_on_term, Function.comp_app]
    rfl
    
  · simp only [on_bounded_formula, comp_on_relation, comp_on_term, Function.comp_app]
    rfl
    
  · simp only [on_bounded_formula, Function.comp_app, ih1, ih2, eq_self_iff_true, and_selfₓ]
    
  · simp only [ih3, on_bounded_formula, Function.comp_app]
    

/-- Maps a formula's symbols along a language map. -/
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula

/-- Maps a sentence's symbols along a language map. -/
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula

/-- Maps a theory's symbols along a language map. -/
def OnTheory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T

@[simp]
theorem mem_on_Theory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ ∈ g.OnTheory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _

end Lhom

namespace Lequiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α n ≃ L'.BoundedFormula α n where
  toFun := φ.toLhom.onBoundedFormula
  invFun := φ.invLhom.onBoundedFormula
  left_inv := by
    rw [Function.left_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.left_inv, Lhom.id_on_bounded_formula]
  right_inv := by
    rw [Function.right_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.right_inv, Lhom.id_on_bounded_formula]

theorem on_bounded_formula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α n ≃ L.BoundedFormula α n) = φ.symm.onBoundedFormula :=
  rfl

/-- Maps a formula's symbols along a language equivalence. -/
def onFormula (φ : L ≃ᴸ L') : L.Formula α ≃ L'.Formula α :=
  φ.onBoundedFormula

@[simp]
theorem on_formula_apply (φ : L ≃ᴸ L') : (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLhom.onFormula :=
  rfl

@[simp]
theorem on_formula_symm (φ : L ≃ᴸ L') : (φ.onFormula.symm : L'.Formula α ≃ L.Formula α) = φ.symm.onFormula :=
  rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps]
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula

end Lequiv

-- mathport name: «expr =' »
localized [FirstOrder] infixl:88 " =' " => FirstOrder.Language.Term.bdEqual

-- mathport name: «expr ⟹ »
-- input \~- or \simeq
localized [FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.BoundedFormula.imp

-- mathport name: «expr∀' »
-- input \==>
localized [FirstOrder] prefix:110 "∀'" => FirstOrder.Language.BoundedFormula.all

-- mathport name: «expr∼ »
localized [FirstOrder] prefix:arg "∼" => FirstOrder.Language.BoundedFormula.not

-- mathport name: «expr ⇔ »
-- input \~, the ASCII character ~ has too low precedence
localized [FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.BoundedFormula.iff

-- mathport name: «expr∃' »
-- input \<=>
localized [FirstOrder] prefix:110 "∃'" => FirstOrder.Language.BoundedFormula.ex

-- input \ex
namespace Formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.Formula α → L.Formula β :=
  @BoundedFormula.relabelₓ _ _ _ 0 (Sum.inl ∘ g) 0

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

theorem is_atomic_graph (f : L.Functions n) : (graph f).IsAtomic :=
  BoundedFormula.IsAtomic.equal _ _

end Formula

namespace Relations

variable (r : L.Relations 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.Sentence :=
  ∀'r.boundedFormula₂ (&0) &0

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.Sentence :=
  ∀'∼(r.boundedFormula₂ (&0) &0)

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &0 ⟹ Term.bdEqual (&0) &1)

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.Sentence :=
  ∀'∀'∀'(r.boundedFormula₂ (&0) &1 ⟹ r.boundedFormula₂ (&1) &2 ⟹ r.boundedFormula₂ (&0) &2)

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.Sentence :=
  ∀'∀'(r.boundedFormula₂ (&0) &1⊔r.boundedFormula₂ (&1) &0)

end Relations

section Nonempty

variable (L)

/-- A sentence that indicates a structure is nonempty. -/
protected def Sentence.nonempty : L.Sentence :=
  ∃'(&0 =' &0)

/-- A theory that indicates a structure is nonempty. -/
protected def Theory.Nonempty : L.Theory :=
  {Sentence.nonempty L}

end Nonempty

end Language

end FirstOrder

