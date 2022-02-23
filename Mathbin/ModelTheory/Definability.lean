/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Fintype.Basic
import Mathbin.ModelTheory.TermsAndFormulas

/-!
# Definable Sets
This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions
* A `first_order.language.definable_set` is defined so that `L.definable_set M α` is the boolean
  algebra of subsets of `α → M` defined by formulas.

## Main Results
* `L.definable_set M α` forms a `boolean_algebra.

-/


namespace FirstOrder

namespace Language

variable {L : Language} {M : Type _} [L.Structure M]

open_locale FirstOrder

open Structure

/-! ### Definability -/


section Definability

variable (L) {α : Type} [Fintype α]

/-- A subset of a finite Cartesian product of a structure is definable when membership in
  the set is given by a first-order formula. -/
structure IsDefinable (s : Set (α → M)) : Prop where
  exists_formula : ∃ φ : L.Formula α, s = SetOf φ.realize

variable {L}

@[simp]
theorem is_definable_empty : L.IsDefinable (∅ : Set (α → M)) :=
  ⟨⟨⊥, by
      ext
      simp ⟩⟩

@[simp]
theorem is_definable_univ : L.IsDefinable (Set.Univ : Set (α → M)) :=
  ⟨⟨⊤, by
      ext
      simp ⟩⟩

@[simp]
theorem IsDefinable.inter {f g : Set (α → M)} (hf : L.IsDefinable f) (hg : L.IsDefinable g) : L.IsDefinable (f ∩ g) :=
  ⟨by
    rcases hf.exists_formula with ⟨φ, hφ⟩
    rcases hg.exists_formula with ⟨θ, hθ⟩
    refine' ⟨φ⊓θ, _⟩
    ext
    simp [hφ, hθ]⟩

@[simp]
theorem IsDefinable.union {f g : Set (α → M)} (hf : L.IsDefinable f) (hg : L.IsDefinable g) : L.IsDefinable (f ∪ g) :=
  ⟨by
    rcases hf.exists_formula with ⟨φ, hφ⟩
    rcases hg.exists_formula with ⟨θ, hθ⟩
    refine' ⟨φ⊔θ, _⟩
    ext
    rw [hφ, hθ, Set.mem_set_of_eq, formula.realize_sup, Set.mem_union_eq, Set.mem_set_of_eq, Set.mem_set_of_eq]⟩

@[simp]
theorem IsDefinable.compl {s : Set (α → M)} (hf : L.IsDefinable s) : L.IsDefinable (sᶜ) :=
  ⟨by
    rcases hf.exists_formula with ⟨φ, hφ⟩
    refine' ⟨φ.not, _⟩
    rw [hφ]
    rfl⟩

@[simp]
theorem IsDefinable.sdiff {s t : Set (α → M)} (hs : L.IsDefinable s) (ht : L.IsDefinable t) : L.IsDefinable (s \ t) :=
  hs.inter ht.Compl

variable (L) (M) (α)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def DefinableSet :=
  Subtype fun s : Set (α → M) => IsDefinable L s

namespace DefinableSet

variable {M} {α}

instance : HasTop (L.DefinableSet M α) :=
  ⟨⟨⊤, is_definable_univ⟩⟩

instance : HasBot (L.DefinableSet M α) :=
  ⟨⟨⊥, is_definable_empty⟩⟩

instance : Inhabited (L.DefinableSet M α) :=
  ⟨⊥⟩

instance : SetLike (L.DefinableSet M α) (α → M) where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

@[simp]
theorem mem_top {x : α → M} : x ∈ (⊤ : L.DefinableSet M α) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.DefinableSet M α) : Set (α → M)) = ⊤ :=
  rfl

@[simp]
theorem not_mem_bot {x : α → M} : ¬x ∈ (⊥ : L.DefinableSet M α) :=
  Set.not_mem_empty x

@[simp]
theorem coe_bot : ((⊥ : L.DefinableSet M α) : Set (α → M)) = ⊥ :=
  rfl

instance : Lattice (L.DefinableSet M α) :=
  Subtype.lattice (fun _ _ => IsDefinable.union) fun _ _ => IsDefinable.inter

theorem le_iff {s t : L.DefinableSet M α} : s ≤ t ↔ (s : Set (α → M)) ≤ (t : Set (α → M)) :=
  Iff.rfl

@[simp]
theorem coe_sup {s t : L.DefinableSet M α} : ((s⊔t : L.DefinableSet M α) : Set (α → M)) = s ∪ t :=
  rfl

@[simp]
theorem mem_sup {s t : L.DefinableSet M α} {x : α → M} : x ∈ s⊔t ↔ x ∈ s ∨ x ∈ t :=
  Iff.rfl

@[simp]
theorem coe_inf {s t : L.DefinableSet M α} : ((s⊓t : L.DefinableSet M α) : Set (α → M)) = s ∩ t :=
  rfl

@[simp]
theorem mem_inf {s t : L.DefinableSet M α} {x : α → M} : x ∈ s⊓t ↔ x ∈ s ∧ x ∈ t :=
  Iff.rfl

instance : BoundedOrder (L.DefinableSet M α) :=
  { DefinableSet.hasTop L, DefinableSet.hasBot L with bot_le := fun s x hx => False.elim hx,
    le_top := fun s x hx => Set.mem_univ x }

instance : DistribLattice (L.DefinableSet M α) :=
  { DefinableSet.lattice L with
    le_sup_inf := by
      intro s t u x
      simp only [and_imp, Set.mem_inter_eq, SetLike.mem_coe, coe_sup, coe_inf, Set.mem_union_eq, Subtype.val_eq_coe]
      tauto }

/-- The complement of a definable set is also definable. -/
@[reducible]
instance : HasCompl (L.DefinableSet M α) :=
  ⟨fun ⟨s, hs⟩ => ⟨sᶜ, hs.Compl⟩⟩

@[simp]
theorem mem_compl {s : L.DefinableSet M α} {x : α → M} : x ∈ sᶜ ↔ ¬x ∈ s := by
  cases' s with s hs
  rfl

@[simp]
theorem coe_compl {s : L.DefinableSet M α} : ((sᶜ : L.DefinableSet M α) : Set (α → M)) = sᶜ := by
  ext
  simp

instance : BooleanAlgebra (L.DefinableSet M α) :=
  { DefinableSet.hasCompl L, DefinableSet.boundedOrder L, DefinableSet.distribLattice L with sdiff := fun s t => s⊓tᶜ,
    sdiff_eq := fun s t => rfl,
    sup_inf_sdiff := fun ⟨s, hs⟩ ⟨t, ht⟩ => by
      apply le_antisymmₓ <;> simp [le_iff],
    inf_inf_sdiff := fun ⟨s, hs⟩ ⟨t, ht⟩ => by
      rw [eq_bot_iff]
      simp only [coe_compl, le_iff, coe_bot, coe_inf, Subtype.coe_mk, Set.le_eq_subset]
      intro x hx
      simp only [Set.mem_inter_eq, Set.mem_compl_eq] at hx
      tauto,
    inf_compl_le_bot := fun ⟨s, hs⟩ => by
      simp [le_iff],
    top_le_sup_compl := fun ⟨s, hs⟩ => by
      simp [le_iff] }

end DefinableSet

end Definability

end Language

end FirstOrder

