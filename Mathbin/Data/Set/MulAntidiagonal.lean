/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Order.WellFoundedSet

/-! # Multiplication antidiagonal -/


namespace Set

variable {α : Type _}

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Set α} {a : α} {x : α × α}

/-- `set.mul_antidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that multiply to `a`. -/
@[to_additive
      "`set.add_antidiagonal s t a` is the set of all pairs of an element in `s` and an\nelement in `t` that add to `a`."]
def MulAntidiagonal (s t : Set α) (a : α) : Set (α × α) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a }

@[simp, to_additive]
theorem mem_mul_antidiagonal : x ∈ MulAntidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a :=
  Iff.rfl

@[to_additive]
theorem mul_antidiagonal_mono_left (h : s₁ ⊆ s₂) : MulAntidiagonal s₁ t a ⊆ MulAntidiagonal s₂ t a := fun x hx =>
  ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
theorem mul_antidiagonal_mono_right (h : t₁ ⊆ t₂) : MulAntidiagonal s t₁ a ⊆ MulAntidiagonal s t₂ a := fun x hx =>
  ⟨hx.1, h hx.2.1, hx.2.2⟩

end Mul

@[simp, to_additive]
theorem swap_mem_mul_antidiagonal [CommSemigroup α] {s t : Set α} {a : α} {x : α × α} :
    x.swap ∈ Set.MulAntidiagonal s t a ↔ x ∈ Set.MulAntidiagonal t s a := by simp [mul_comm, and_left_comm]

namespace MulAntidiagonal

section CancelCommMonoid

variable [CancelCommMonoid α] {s t : Set α} {a : α} {x y : MulAntidiagonal s t a}

@[to_additive]
theorem fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2 :=
  ⟨fun h =>
    mul_left_cancel
      (y.Prop.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    mul_right_cancel
      (y.Prop.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive]
theorem eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive]
theorem eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] (s t : Set α) (a : α) {x y : MulAntidiagonal s t a}

@[to_additive]
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 ≤ (y : α × α).1) (h₂ : (x : α × α).2 ≤ (y : α × α).2) :
    x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (mul_lt_mul_of_lt_of_le hlt h₂).Ne <| (mem_mul_antidiagonal.1 x.2).2.2.trans (mem_mul_antidiagonal.1 y.2).2.2.symm

variable {s t}

@[to_additive]
theorem finite_of_is_pwo (hs : s.IsPwo) (ht : t.IsPwo) (a) : (MulAntidiagonal s t a).Finite := by
  refine' not_infinite.1 fun h => _
  have h1 : (mul_antidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) := fun f hf =>
    hs (Prod.fst ∘ f) fun n => (mem_mul_antidiagonal.1 (hf n)).1
  have h2 : (mul_antidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) := fun f hf =>
    ht (Prod.snd ∘ f) fun n => (mem_mul_antidiagonal.1 (hf n)).2.1
  obtain ⟨g, hg⟩ := h1.exists_monotone_subseq (fun n => h.nat_embedding _ n) fun n => (h.nat_embedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 (fun x => (h.nat_embedding _) (g x)) fun n => (h.nat_embedding _ _).2
  refine' mn.ne (g.injective <| (h.nat_embedding _).Injective _)
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'

end OrderedCancelCommMonoid

@[to_additive]
theorem finite_of_is_wf [LinearOrderedCancelCommMonoid α] {s t : Set α} (hs : s.IsWf) (ht : t.IsWf) (a) :
    (MulAntidiagonal s t a).Finite :=
  finite_of_is_pwo hs.IsPwo ht.IsPwo a

end MulAntidiagonal

end Set

