/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.Ultraproducts
import Mathbin.ModelTheory.Bundled
import Mathbin.ModelTheory.Skolem

/-!
# First-Order Satisfiability
This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions
* `first_order.language.Theory.is_satisfiable`: `T.is_satisfiable` indicates that `T` has a nonempty
model.
* `first_order.language.Theory.is_finitely_satisfiable`: `T.is_finitely_satisfiable` indicates that
every finite subset of `T` is satisfiable.
* `first_order.language.Theory.semantically_equivalent`: `T.semantically_equivalent φ ψ` indicates
that `φ` and `ψ` are equivalent formulas or sentences in models of `T`.

## Main Results
* The Compactness Theorem, `first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable`,
shows that a theory is satisfiable iff it is finitely satisfiable.

## Implementation Details
* Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe, but this is not
yet proven in mathlib.

-/


universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type _} {n : ℕ}

namespace Theory

variable (T)

/-- A theory is satisfiable if a structure models it. -/
def IsSatisfiable : Prop :=
  Nonempty (ModelCat.{u, v, max u v} T)

/-- A theory is finitely satisfiable if all of its finite subtheories are satisfiable. -/
def IsFinitelySatisfiable : Prop :=
  ∀ T0 : Finset L.Sentence, (T0 : L.Theory) ⊆ T → (T0 : L.Theory).IsSatisfiable

variable {T} {T' : L.Theory}

theorem Model.is_satisfiable (M : Type w) [n : Nonempty M] [S : L.Structure M] [M ⊨ T] : T.IsSatisfiable :=
  ⟨((⊥ : Substructure _ (ModelCat.of T M)).elementarySkolem₁Reduct.toModel T).Shrink⟩

theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T ⊆ T') : T.IsSatisfiable :=
  ⟨(Theory.Model.mono (ModelCat.is_model h.some) hs).Bundled⟩

theorem IsSatisfiable.is_finitely_satisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable := fun _ => h.mono

/-- The Compactness Theorem of first-order logic: A theory is satisfiable if and only if it is
finitely satisfiable. -/
theorem is_satisfiable_iff_is_finitely_satisfiable {T : L.Theory} : T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  ⟨Theory.IsSatisfiable.is_finitely_satisfiable, fun h => by
    classical
    set M : ∀ T0 : Finset T, Type max u v := fun T0 =>
      (h (T0.map (Function.Embedding.subtype fun x => x ∈ T)) T0.map_subtype_subset).some with hM
    let M' := Filter.Product (↑(Ultrafilter.of (Filter.atTop : Filter (Finset T)))) M
    have h' : M' ⊨ T := by
      refine' ⟨fun φ hφ => _⟩
      rw [ultraproduct.sentence_realize]
      refine'
        Filter.Eventually.filter_mono (Ultrafilter.of_le _)
          (Filter.eventually_at_top.2
            ⟨{⟨φ, hφ⟩}, fun s h' =>
              Theory.realize_sentence_of_mem (s.map (Function.Embedding.subtype fun x => x ∈ T)) _⟩)
      simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe, Subtype.exists,
        Subtype.coe_mk, exists_and_distrib_right, exists_eq_right]
      exact ⟨hφ, h' (Finset.mem_singleton_self _)⟩
    exact ⟨Model.of T M'⟩⟩

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs.-/
def ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop :=
  ∀ M : ModelCat.{u, v, max u v} T v : α → M xs : Finₓ n → M, φ.realize v xs

-- mathport name: «expr ⊨ »
infixl:51 " ⊨ " => ModelsBoundedFormula

-- input using \|= or \vDash, but not using \models
variable {T}

theorem models_formula_iff {φ : L.Formula α} : T ⊨ φ ↔ ∀ M : ModelCat.{u, v, max u v} T v : α → M, φ.realize v :=
  forall_congrₓ fun M => forall_congrₓ fun v => Unique.forall_iff

theorem models_sentence_iff {φ : L.Sentence} : T ⊨ φ ↔ ∀ M : ModelCat.{u, v, max u v} T, M ⊨ φ :=
  models_formula_iff.trans (forall_congrₓ fun M => Unique.forall_iff)

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def SemanticallyEquivalent (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ φ.Iff ψ

@[refl]
theorem SemanticallyEquivalent.refl (φ : L.BoundedFormula α n) : T.SemanticallyEquivalent φ φ := fun M v xs => by
  rw [bounded_formula.realize_iff]

instance : IsRefl (L.BoundedFormula α n) T.SemanticallyEquivalent :=
  ⟨SemanticallyEquivalent.refl⟩

@[symm]
theorem SemanticallyEquivalent.symm {φ ψ : L.BoundedFormula α n} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent ψ φ := fun M v xs => by
  rw [bounded_formula.realize_iff, Iff.comm, ← bounded_formula.realize_iff]
  exact h M v xs

@[trans]
theorem SemanticallyEquivalent.trans {φ ψ θ : L.BoundedFormula α n} (h1 : T.SemanticallyEquivalent φ ψ)
    (h2 : T.SemanticallyEquivalent ψ θ) : T.SemanticallyEquivalent φ θ := fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [bounded_formula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩

theorem SemanticallyEquivalent.realize_bd_iff {φ ψ : L.BoundedFormula α n} {M : Type max u v} [ne : Nonempty M]
    [str : L.Structure M] [hM : T.Model M] (h : T.SemanticallyEquivalent φ ψ) {v : α → M} {xs : Finₓ n → M} :
    φ.realize v xs ↔ ψ.realize v xs :=
  BoundedFormula.realize_iff.1 (h (ModelCat.of T M) v xs)

theorem SemanticallyEquivalent.realize_iff {φ ψ : L.Formula α} {M : Type max u v} [ne : Nonempty M]
    [str : L.Structure M] (hM : T.Model M) (h : T.SemanticallyEquivalent φ ψ) {v : α → M} : φ.realize v ↔ ψ.realize v :=
  h.realize_bd_iff

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semanticallyEquivalentSetoid (T : L.Theory) : Setoidₓ (L.BoundedFormula α n) where
  R := SemanticallyEquivalent T
  iseqv := ⟨fun _ => refl _, fun a b h => h.symm, fun _ _ _ h1 h2 => h1.trans h2⟩

protected theorem SemanticallyEquivalent.all {φ ψ : L.BoundedFormula α (n + 1)} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent φ.all ψ.all := by
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff, bounded_formula.realize_all]
  exact fun M v xs => forall_congrₓ fun a => h.realize_bd_iff

protected theorem SemanticallyEquivalent.ex {φ ψ : L.BoundedFormula α (n + 1)} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent φ.ex ψ.ex := by
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff, bounded_formula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff

protected theorem SemanticallyEquivalent.not {φ ψ : L.BoundedFormula α n} (h : T.SemanticallyEquivalent φ ψ) :
    T.SemanticallyEquivalent φ.Not ψ.Not := by
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff, bounded_formula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff

protected theorem SemanticallyEquivalent.imp {φ ψ φ' ψ' : L.BoundedFormula α n} (h : T.SemanticallyEquivalent φ ψ)
    (h' : T.SemanticallyEquivalent φ' ψ') : T.SemanticallyEquivalent (φ.imp φ') (ψ.imp ψ') := by
  simp_rw [semantically_equivalent, models_bounded_formula, bounded_formula.realize_iff, bounded_formula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff

end Theory

namespace BoundedFormula

variable (φ ψ : L.BoundedFormula α n)

theorem semantically_equivalent_not_not : T.SemanticallyEquivalent φ φ.Not.Not := fun M v xs => by
  simp

theorem imp_semantically_equivalent_not_sup : T.SemanticallyEquivalent (φ.imp ψ) (φ.Not⊔ψ) := fun M v xs => by
  simp [imp_iff_not_or]

theorem sup_semantically_equivalent_not_inf_not : T.SemanticallyEquivalent (φ⊔ψ) (φ.Not⊓ψ.Not).Not := fun M v xs => by
  simp [imp_iff_not_or]

theorem inf_semantically_equivalent_not_sup_not : T.SemanticallyEquivalent (φ⊓ψ) (φ.Not⊔ψ.Not).Not := fun M v xs => by
  simp [and_iff_not_or_not]

theorem all_semantically_equivalent_not_ex_not (φ : L.BoundedFormula α (n + 1)) :
    T.SemanticallyEquivalent φ.all φ.Not.ex.Not := fun M v xs => by
  simp

theorem ex_semantically_equivalent_not_all_not (φ : L.BoundedFormula α (n + 1)) :
    T.SemanticallyEquivalent φ.ex φ.Not.all.Not := fun M v xs => by
  simp

theorem semantically_equivalent_all_lift_at : T.SemanticallyEquivalent φ (φ.liftAt 1 n).all := fun M v xs => by
  skip
  rw [realize_iff, realize_all_lift_at_one_self]

end BoundedFormula

namespace Formula

variable (φ ψ : L.Formula α)

theorem semantically_equivalent_not_not : T.SemanticallyEquivalent φ φ.Not.Not :=
  φ.semantically_equivalent_not_not

theorem imp_semantically_equivalent_not_sup : T.SemanticallyEquivalent (φ.imp ψ) (φ.Not⊔ψ) :=
  φ.imp_semantically_equivalent_not_sup ψ

theorem sup_semantically_equivalent_not_inf_not : T.SemanticallyEquivalent (φ⊔ψ) (φ.Not⊓ψ.Not).Not :=
  φ.sup_semantically_equivalent_not_inf_not ψ

theorem inf_semantically_equivalent_not_sup_not : T.SemanticallyEquivalent (φ⊓ψ) (φ.Not⊔ψ.Not).Not :=
  φ.inf_semantically_equivalent_not_sup_not ψ

end Formula

namespace BoundedFormula

theorem IsQf.induction_on_sup_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} (h : IsQf φ)
    (hf : P (⊥ : L.BoundedFormula α n)) (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hsup : ∀ {φ₁ φ₂} h₁ : P φ₁ h₂ : P φ₂, P (φ₁⊔φ₂)) (hnot : ∀ {φ} h : P φ, P φ.Not)
    (hse : ∀ {φ₁ φ₂ : L.BoundedFormula α n} h : Theory.SemanticallyEquivalent ∅ φ₁ φ₂, P φ₁ ↔ P φ₂) : P φ :=
  IsQf.rec_on h hf ha fun φ₁ φ₂ _ _ h1 h2 => (hse (φ₁.imp_semantically_equivalent_not_sup φ₂)).2 (hsup (hnot h1) h2)

theorem IsQf.induction_on_inf_not {P : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} (h : IsQf φ)
    (hf : P (⊥ : L.BoundedFormula α n)) (ha : ∀ ψ : L.BoundedFormula α n, IsAtomic ψ → P ψ)
    (hinf : ∀ {φ₁ φ₂} h₁ : P φ₁ h₂ : P φ₂, P (φ₁⊓φ₂)) (hnot : ∀ {φ} h : P φ, P φ.Not)
    (hse : ∀ {φ₁ φ₂ : L.BoundedFormula α n} h : Theory.SemanticallyEquivalent ∅ φ₁ φ₂, P φ₁ ↔ P φ₂) : P φ :=
  h.induction_on_sup_not hf ha
    (fun φ₁ φ₂ h1 h2 => (hse (φ₁.sup_semantically_equivalent_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2))))
    (fun _ => hnot) fun _ _ => hse

theorem semantically_equivalent_to_prenex (φ : L.BoundedFormula α n) :
    (∅ : L.Theory).SemanticallyEquivalent φ φ.toPrenex := fun M v xs => by
  rw [realize_iff, realize_to_prenex]

theorem induction_on_all_ex {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQf ψ → P ψ)
    (hall : ∀ {m} {ψ : L.BoundedFormula α (m + 1)} h : P ψ, P ψ.all)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)} h : P φ, P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m} h : Theory.SemanticallyEquivalent ∅ φ₁ φ₂, P φ₁ ↔ P φ₂) : P φ := by
  suffices h' : ∀ {m} {φ : L.bounded_formula α m}, φ.IsPrenex → P φ
  · exact (hse φ.semantically_equivalent_to_prenex).2 (h' φ.to_prenex_is_prenex)
    
  intro m φ hφ
  induction' hφ with _ _ hφ _ _ _ hφ _ _ _ hφ
  · exact hqf hφ
    
  · exact hall hφ
    
  · exact hex hφ
    

theorem induction_on_exists_not {P : ∀ {m}, L.BoundedFormula α m → Prop} (φ : L.BoundedFormula α n)
    (hqf : ∀ {m} {ψ : L.BoundedFormula α m}, IsQf ψ → P ψ) (hnot : ∀ {m} {φ : L.BoundedFormula α m} h : P φ, P φ.Not)
    (hex : ∀ {m} {φ : L.BoundedFormula α (m + 1)} h : P φ, P φ.ex)
    (hse : ∀ {m} {φ₁ φ₂ : L.BoundedFormula α m} h : Theory.SemanticallyEquivalent ∅ φ₁ φ₂, P φ₁ ↔ P φ₂) : P φ :=
  φ.induction_on_all_ex (fun _ _ => hqf)
    (fun _ φ hφ => (hse φ.all_semantically_equivalent_not_ex_not).2 (hnot (hex (hnot hφ)))) (fun _ _ => hex)
    fun _ _ _ => hse

end BoundedFormula

end Language

end FirstOrder

