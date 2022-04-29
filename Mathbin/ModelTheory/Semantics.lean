/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathbin.Data.Finset.Basic
import Mathbin.ModelTheory.Syntax

/-!
# Basics on First-Order Semantics
This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions
* `first_order.language.term.realize` is defined so that `t.realize v` is the term `t` evaluated at
variables `v`.
* `first_order.language.bounded_formula.realize` is defined so that `φ.realize v xs` is the bounded
formula `φ` evaluated at tuples of variables `v` and `xs`.
* `first_order.language.formula.realize` is defined so that `φ.realize v` is the formula `φ`
evaluated at variables `v`.
* `first_order.language.sentence.realize` is defined so that `φ.realize M` is the sentence `φ`
evaluated in the structure `M`. Also denoted `M ⊨ φ`.
* `first_order.language.Theory.model` is defined so that `T.model M` is true if and only if every
sentence of `T` is realized in `M`. Also denoted `T ⊨ φ`.

## Main Results
* `first_order.language.bounded_formula.realize_to_prenex` shows that the prenex normal form of a
formula has the same realization as the original formula.
* Several results in this file show that syntactic constructions such as `relabel`, `cast_le`,
`lift_at`, and the actions of language maps commute with realization of terms, formulas, sentences,
and theories.

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

variable {L : Language.{u, v}} {L' : Language}

variable {M : Type w} {N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'}

open FirstOrder Cardinal

open Structure Cardinal Finₓ

namespace Term

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
    

@[simp]
theorem realize_lift_at {n n' m : ℕ} {t : L.Term (Sum α (Finₓ n))} {v : Sum α (Finₓ (n + n')) → M} :
    (t.liftAt n' m).realize v =
      t.realize (v ∘ Sum.map id fun i => if ↑i < m then Finₓ.castAdd n' i else Finₓ.addNat n' i) :=
  realize_relabel

@[simp]
theorem realize_constants {c : L.Constants} {v : α → M} : c.Term.realize v = c :=
  fun_map_eq_coe_constants

@[simp]
theorem realize_functions_apply₁ {f : L.Functions 1} {t : L.Term α} {v : α → M} :
    (f.apply₁ t).realize v = funMap f ![t.realize v] := by
  rw [functions.apply₁, term.realize]
  refine' congr rfl (funext fun i => _)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_functions_apply₂ {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α → M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ![t₁.realize v, t₂.realize v] := by
  rw [functions.apply₂, term.realize]
  refine' congr rfl (funext (Finₓ.cases _ _))
  · simp only [Matrix.cons_val_zero]
    
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
    

theorem realize_con {A : Set M} {a : A} {v : α → M} : (L.con a).Term.realize v = a :=
  rfl

end Term

namespace Lhom

@[simp]
theorem realize_on_term [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.Term α) (v : α → M) :
    (φ.onTerm t).realize v = t.realize v := by
  induction' t with _ n f ts ih
  · rfl
    
  · simp only [term.realize, Lhom.on_term, Lhom.is_expansion_on.map_on_function, ih]
    

end Lhom

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

variable {L} {α} {n : ℕ}

namespace BoundedFormula

open Term

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def Realizeₓ : ∀ {l} f : L.BoundedFormula α l v : α → M xs : Finₓ l → M, Prop
  | _, falsum, v, xs => False
  | _, bounded_formula.equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, bounded_formula.rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, bounded_formula.imp f₁ f₂, v, xs => realize f₁ v xs → realize f₂ v xs
  | _, bounded_formula.all f, v, xs => ∀ x : M, realize f v (snoc xs x)

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
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.boundedFormula₁ t).realize v xs ↔ RelMap R ![t.realize (Sum.elim v xs)] := by
  rw [relations.bounded_formula₁, realize_rel, iff_eq_eq]
  refine' congr rfl (funext fun _ => _)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.boundedFormula₂ t₁ t₂).realize v xs ↔ RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  rw [relations.bounded_formula₂, realize_rel, iff_eq_eq]
  refine' congr rfl (funext (Finₓ.cases _ _))
  · simp only [Matrix.cons_val_zero]
    
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
    

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

theorem realize_cast_le_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} {φ : L.BoundedFormula α m} {v : α → M}
    {xs : Finₓ n → M} : (φ.cast_le h').realize v xs ↔ φ.realize v (xs ∘ Finₓ.cast h) := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 k _ ih3 generalizing n xs h h'
  · simp [cast_le, realize]
    
  · simp only [cast_le, realize, realize_bd_equal, term.realize_relabel, Sum.elim_comp_map, Function.comp.right_id,
      cast_le_of_eq h]
    
  · simp only [cast_le, realize, realize_rel, term.realize_relabel, Sum.elim_comp_map, Function.comp.right_id,
      cast_le_of_eq h]
    
  · simp only [cast_le, realize, ih1 h, ih2 h]
    
  · simp only [cast_le, realize, ih3 (Nat.succ_inj'.2 h)]
    refine' forall_congrₓ fun x => iff_eq_eq.mpr (congr rfl (funext (last_cases _ fun i => _)))
    · rw [Function.comp_app, snoc_last, cast_last, snoc_last]
      
    · rw [Function.comp_app, snoc_cast_succ, cast_cast_succ, snoc_cast_succ]
      
    

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
        
      
    

theorem realize_lift_at {n n' m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Finₓ (n + n') → M}
    (hmn : m + n' ≤ n + 1) :
    (φ.liftAt n' m).realize v xs ↔ φ.realize v (xs ∘ fun i => if ↑i < m then Finₓ.castAdd n' i else Finₓ.addNat n' i) :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 k _ ih3
  · simp [lift_at, realize]
    
  · simp only [lift_at, realize, realize_bd_equal, realize_lift_at, Sum.elim_comp_map, Function.comp.right_id]
    
  · simp only [lift_at, realize, realize_rel, realize_lift_at, Sum.elim_comp_map, Function.comp.right_id]
    
  · simp only [lift_at, realize, ih1 hmn, ih2 hmn]
    
  · have h : k + 1 + n' = k + n' + 1 := by
      rw [add_assocₓ, add_commₓ 1 n', ← add_assocₓ]
    simp only [lift_at, realize, realize_cast_le_of_eq h, ih3 (hmn.trans k.succ.le_succ)]
    refine' forall_congrₓ fun x => iff_eq_eq.mpr (congr rfl (funext (Finₓ.lastCases _ fun i => _)))
    · simp only [Function.comp_app, coe_last, snoc_last]
      by_cases' k < m
      · rw [if_pos h]
        refine' (congr rfl (ext _)).trans (snoc_last _ _)
        simp only [coe_cast, coe_cast_add, coe_last, self_eq_add_rightₓ]
        refine' le_antisymmₓ (le_of_add_le_add_left ((hmn.trans (Nat.succ_le_of_ltₓ h)).trans _)) n'.zero_le
        rw [add_zeroₓ]
        
      · rw [if_neg h]
        refine' (congr rfl (ext _)).trans (snoc_last _ _)
        simp
        
      
    · simp only [Function.comp_app, Finₓ.snoc_cast_succ]
      refine' (congr rfl (ext _)).trans (snoc_cast_succ _ _ _)
      simp only [cast_refl, coe_cast_succ, OrderIso.coe_refl, id.def]
      split_ifs <;> simp
      
    

theorem realize_lift_at_one {n m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Finₓ (n + 1) → M} (hmn : m ≤ n) :
    (φ.liftAt 1 m).realize v xs ↔ φ.realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) := by
  simp_rw [realize_lift_at (add_le_add_right hmn 1), cast_succ, add_nat_one]

@[simp]
theorem realize_lift_at_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Finₓ (n + 1) → M} :
    (φ.liftAt 1 n).realize v xs ↔ φ.realize v (xs ∘ cast_succ) := by
  rw [realize_lift_at_one (refl n), iff_eq_eq]
  refine' congr rfl (congr rfl (funext fun i => _))
  rw [if_pos i.is_lt]

theorem realize_all_lift_at_one_self [Nonempty M] {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Finₓ n → M} :
    (φ.liftAt 1 n).all.realize v xs ↔ φ.realize v xs := by
  inhabit M
  simp only [realize_all, realize_lift_at_one_self]
  refine' ⟨fun h => _, fun h a => _⟩
  · refine' (congr rfl (funext fun i => _)).mp (h default)
    simp
    
  · refine' (congr rfl (funext fun i => _)).mp h
    simp
    

variable [Nonempty M]

theorem realize_to_prenex_imp_right {φ ψ : L.BoundedFormula α n} (hφ : IsQf φ) (hψ : IsPrenex ψ) {v : α → M}
    {xs : Finₓ n → M} : (φ.toPrenexImpRight ψ).realize v xs ↔ (φ.imp ψ).realize v xs := by
  revert φ
  induction' hψ with _ _ hψ _ _ hψ ih _ _ hψ ih <;> intro φ hφ
  · rw [hψ.to_prenex_imp_right]
    
  · refine' trans (forall_congrₓ fun _ => ih hφ.lift_at) _
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
    
  · rw [to_prenex_imp_right, realize_ex]
    refine' trans (exists_congr fun _ => ih hφ.lift_at) _
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_ex]
    refine' ⟨_, fun h' => _⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
      
    · by_cases' φ.realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
        
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩
        
      
    

theorem realize_to_prenex_imp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) {v : α → M}
    {xs : Finₓ n → M} : (φ.toPrenexImp ψ).realize v xs ↔ (φ.imp ψ).realize v xs := by
  revert ψ
  induction' hφ with _ _ hφ _ _ hφ ih _ _ hφ ih <;> intro ψ hψ
  · rw [hφ.to_prenex_imp]
    exact realize_to_prenex_imp_right hφ hψ
    
  · rw [to_prenex_imp, realize_ex]
    refine' trans (exists_congr fun _ => ih hψ.lift_at) _
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_all]
    refine' ⟨_, fun h' => _⟩
    · rintro ⟨a, ha⟩ h
      exact ha (h a)
      
    · by_cases' ψ.realize v xs
      · inhabit M
        exact ⟨default, fun h'' => h⟩
        
      · obtain ⟨a, ha⟩ := not_forall.1 (h ∘ h')
        exact ⟨a, fun h => (ha h).elim⟩
        
      
    
  · refine' trans (forall_congrₓ fun _ => ih hψ.lift_at) _
    simp
    

@[simp]
theorem realize_to_prenex (φ : L.BoundedFormula α n) {v : α → M} :
    ∀ {xs : Finₓ n → M}, φ.toPrenex.realize v xs ↔ φ.realize v xs := by
  refine'
    bounded_formula.rec_on φ (fun _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => Iff.rfl)
      (fun _ f1 f2 h1 h2 _ => _) fun _ f h xs => _
  · rw [to_prenex, realize_to_prenex_imp f1.to_prenex_is_prenex f2.to_prenex_is_prenex, realize_imp, realize_imp, h1,
      h2]
    infer_instance
    
  · rw [realize_all, to_prenex, realize_all]
    exact forall_congrₓ fun a => h
    

end BoundedFormula

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel

attribute [protected] bounded_formula.imp bounded_formula.all

namespace Lhom

open BoundedFormula

@[simp]
theorem realize_on_bounded_formula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] {n : ℕ} (ψ : L.BoundedFormula α n)
    {v : α → M} {xs : Finₓ n → M} : (φ.onBoundedFormula ψ).realize v xs ↔ ψ.realize v xs := by
  induction' ψ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    
  · simp only [on_bounded_formula, realize_bd_equal, realize_on_term]
    rfl
    
  · simp only [on_bounded_formula, realize_rel, realize_on_term, is_expansion_on.map_on_relation]
    rfl
    
  · simp only [on_bounded_formula, ih1, ih2, realize_imp]
    
  · simp only [on_bounded_formula, ih3, realize_all]
    

end Lhom

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel

attribute [protected] bounded_formula.imp bounded_formula.all

namespace Formula

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
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} : (R.formula₁ t).realize v ↔ RelMap R ![t.realize v] := by
  rw [relations.formula₁, realize_rel, iff_eq_eq]
  refine' congr rfl (funext fun _ => _)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.formula₂ t₁ t₂).realize v ↔ RelMap R ![t₁.realize v, t₂.realize v] := by
  rw [relations.formula₂, realize_rel, iff_eq_eq]
  refine' congr rfl (funext (Finₓ.cases _ _))
  · simp only [Matrix.cons_val_zero]
    
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
    

@[simp]
theorem realize_sup : (φ⊔ψ).realize v ↔ φ.realize v ∨ ψ.realize v :=
  bounded_formula.realize_sup

@[simp]
theorem realize_iff : (φ.Iff ψ).realize v ↔ (φ.realize v ↔ ψ.realize v) :=
  bounded_formula.realize_iff

@[simp]
theorem realize_relabel {φ : L.Formula α} {g : α → β} {v : β → M} : (φ.relabel g).realize v ↔ φ.realize (v ∘ g) := by
  rw [realize, realize, relabel, bounded_formula.realize_relabel, iff_eq_eq, Finₓ.cast_add_zero]
  exact congr rfl (funext finZeroElim)

theorem realize_relabel_sum_inr (φ : L.Formula (Finₓ n)) {v : Empty → M} {x : Finₓ n → M} :
    (BoundedFormula.relabelₓ Sum.inr φ).realize v x ↔ φ.realize x := by
  rw [bounded_formula.realize_relabel, formula.realize, Sum.elim_comp_inr, Finₓ.cast_add_zero, cast_refl,
    OrderIso.coe_refl, Function.comp.right_id, Subsingleton.elimₓ (x ∘ (nat_add n : Finₓ 0 → Finₓ n)) default]

@[simp]
theorem realize_equal {t₁ t₂ : L.Term α} {x : α → M} : (t₁.equal t₂).realize x ↔ t₁.realize x = t₂.realize x := by
  simp [term.equal, realize]

@[simp]
theorem realize_graph {f : L.Functions n} {x : Finₓ n → M} {y : M} :
    (Formula.graph f).realize (Finₓ.cons y x : _ → M) ↔ funMap f x = y := by
  simp only [formula.graph, term.realize, realize_equal, Finₓ.cons_zero, Finₓ.cons_succ]
  rw [eq_comm]

end Formula

@[simp]
theorem Lhom.realize_on_formula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α) {v : α → M} :
    (φ.onFormula ψ).realize v ↔ ψ.realize v :=
  φ.realize_on_bounded_formula ψ

@[simp]
theorem Lhom.set_of_realize_on_formula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α) :
    (SetOf (φ.onFormula ψ).realize : Set (α → M)) = SetOf ψ.realize := by
  ext
  simp

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.realize (default : _ → M)

-- mathport name: «expr ⊨ »
infixl:51 " ⊨ " => Sentence.Realize

-- input using \|= or \vDash, but not using \models
@[simp]
theorem Lhom.realize_on_sentence [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (ψ : L.Sentence) :
    M ⊨ φ.onSentence ψ ↔ M ⊨ ψ :=
  φ.realize_on_formula ψ

/-- A model of a theory is a structure in which every sentence is realized as true. -/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : ∀, ∀ φ ∈ T, ∀, M ⊨ φ

-- mathport name: «expr ⊨ »
infixl:51 " ⊨ " => Theory.Model

-- input using \|= or \vDash, but not using \models
variable {M} (T : L.Theory)

@[simp]
theorem Theory.model_iff : M ⊨ T ↔ ∀, ∀ φ ∈ T, ∀, M ⊨ φ :=
  ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩

theorem Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ ∈ T) : M ⊨ φ :=
  Theory.Model.realize_of_mem φ h

@[simp]
theorem Lhom.on_Theory_model [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (T : L.Theory) :
    M ⊨ φ.OnTheory T ↔ M ⊨ T := by
  simp [Theory.model_iff, Lhom.on_Theory]

variable {M} {T}

instance model_empty : M ⊨ (∅ : L.Theory) :=
  ⟨fun φ hφ => (Set.not_mem_empty φ hφ).elim⟩

theorem Theory.Model.mono {T' : L.Theory} (h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T :=
  ⟨fun φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩

theorem Theory.model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by
  simp

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

namespace Equivₓ

@[simp]
theorem realize_bounded_formula (g : M ≃[L] N) (φ : L.BoundedFormula α n) {v : α → M} {xs : Finₓ n → M} :
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
theorem realize_formula (g : M ≃[L] N) (φ : L.Formula α) {v : α → M} : φ.realize (g ∘ v) ↔ φ.realize v := by
  rw [formula.realize, formula.realize, ← g.realize_bounded_formula φ, iff_eq_eq, Unique.eq_default (g ∘ default)]

theorem realize_sentence (g : M ≃[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [sentence.realize, sentence.realize, ← g.realize_formula, Unique.eq_default (g ∘ default)]

theorem Theory_model (g : M ≃[L] N) [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (g.realize_sentence φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

end Equivₓ

namespace Relations

open BoundedFormula

variable {r : L.Relations 2}

@[simp]
theorem realize_reflexive : M ⊨ r.Reflexive ↔ Reflexive fun x y : M => RelMap r ![x, y] :=
  forall_congrₓ fun _ => realize_rel₂

@[simp]
theorem realize_irreflexive : M ⊨ r.Irreflexive ↔ Irreflexive fun x y : M => RelMap r ![x, y] :=
  forall_congrₓ fun _ => not_congr realize_rel₂

@[simp]
theorem realize_symmetric : M ⊨ r.Symmetric ↔ Symmetric fun x y : M => RelMap r ![x, y] :=
  forall_congrₓ fun _ => forall_congrₓ fun _ => imp_congr realize_rel₂ realize_rel₂

@[simp]
theorem realize_antisymmetric : M ⊨ r.antisymmetric ↔ AntiSymmetric fun x y : M => RelMap r ![x, y] :=
  forall_congrₓ fun _ => forall_congrₓ fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ Iff.rfl)

@[simp]
theorem realize_transitive : M ⊨ r.Transitive ↔ Transitive fun x y : M => RelMap r ![x, y] :=
  forall_congrₓ fun _ =>
    forall_congrₓ fun _ => forall_congrₓ fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ realize_rel₂)

@[simp]
theorem realize_total : M ⊨ r.Total ↔ Total fun x y : M => RelMap r ![x, y] :=
  forall_congrₓ fun _ => forall_congrₓ fun _ => realize_sup.trans (or_congr realize_rel₂ realize_rel₂)

end Relations

section Nonempty

variable (L)

@[simp]
theorem Sentence.realize_nonempty : M ⊨ Sentence.nonempty L ↔ Nonempty M :=
  BoundedFormula.realize_ex.trans (trans (exists_congr eq_self_iff_true) exists_true_iff_nonempty)

@[simp]
theorem Theory.model_nonempty_iff : M ⊨ Theory.Nonempty L ↔ Nonempty M :=
  Theory.model_singleton_iff.trans (Sentence.realize_nonempty L)

instance Theory.model_nonempty [h : Nonempty M] : M ⊨ Theory.Nonempty L :=
  (Theory.model_nonempty_iff L).2 h

end Nonempty

end Language

end FirstOrder

