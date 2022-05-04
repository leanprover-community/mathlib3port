/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Order.WellFounded
import Mathbin.Algebra.Group.Pi
import Mathbin.Order.MinMax

/-!
# Lexicographic order on Pi types

This file defines the lexicographic relation for Pi types of partial orders and linear orders. We
also provide a `pilex` analog of `pi.ordered_comm_group` (see `algebra.order.pi`).
-/


variable {ι : Type _} {β : ι → Type _} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
def Pi.Lex (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/-- The cartesian product of an indexed family, equipped with the lexicographic order. -/
def Pilex (α : Type _) (β : α → Type _) : Type _ :=
  ∀ a, β a

instance [LT ι] [∀ a, LT (β a)] : LT (Pilex ι β) where
  lt := Pi.Lex (· < ·) fun _ => (· < ·)

instance [∀ a, Inhabited (β a)] : Inhabited (Pilex ι β) := by
  unfold Pilex <;> infer_instance

instance Pilex.is_strict_order [LinearOrderₓ ι] [∀ a, PartialOrderₓ (β a)] : IsStrictOrder (Pilex ι β) (· < ·) where
  irrefl := fun a ⟨k, hk₁, hk₂⟩ => lt_irreflₓ (a k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    rcases lt_trichotomyₓ N₁ N₂ with (H | rfl | H)
    exacts[⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
      ⟨N₂, fun j hj => (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]

instance [LinearOrderₓ ι] [∀ a, PartialOrderₓ (β a)] : PartialOrderₓ (Pilex ι β) :=
  partialOrderOfSO (· < ·)

protected theorem Pilex.is_strict_total_order' [LinearOrderₓ ι] (wf : WellFounded ((· < ·) : ι → ι → Prop))
    [∀ a, LinearOrderₓ (β a)] : IsStrictTotalOrder' (Pilex ι β) (· < ·) :=
  { trichotomous := fun a b => by
      by_cases' h : ∃ i, a i ≠ b i
      · let i := wf.min _ h
        have hlt_i : ∀, ∀ j < i, ∀, a j = b j := by
          intro j
          rw [← not_imp_not]
          exact fun h' => wf.not_lt_min _ _ h'
        have : a i ≠ b i := wf.min_mem _ h
        exact this.lt_or_lt.imp (fun h => ⟨i, hlt_i, h⟩) fun h => Or.inr ⟨i, fun j hj => (hlt_i j hj).symm, h⟩
        
      · push_neg  at h
        exact Or.inr (Or.inl (funext h))
         }

/-- `pilex` is a linear order if the original order is well-founded.
This cannot be an instance, since it depends on the well-foundedness of `<`. -/
protected noncomputable def Pilex.linearOrder [LinearOrderₓ ι] (wf : WellFounded ((· < ·) : ι → ι → Prop))
    [∀ a, LinearOrderₓ (β a)] : LinearOrderₓ (Pilex ι β) :=
  @linearOrderOfSTO' (Pilex ι β) (· < ·) (Pilex.is_strict_total_order' wf) (Classical.decRel _)

theorem Pilex.le_of_forall_le [LinearOrderₓ ι] (wf : WellFounded ((· < ·) : ι → ι → Prop)) [∀ a, LinearOrderₓ (β a)]
    {a b : Pilex ι β} (h : ∀ i, a i ≤ b i) : a ≤ b := by
  let this : LinearOrderₓ (Pilex ι β) := Pilex.linearOrder wf
  exact le_of_not_ltₓ fun ⟨i, hi⟩ => (h i).not_lt hi.2

--we might want the analog of `pi.ordered_cancel_comm_monoid` as well in the future
@[to_additive]
instance [LinearOrderₓ ι] [∀ a, OrderedCommGroup (β a)] : OrderedCommGroup (Pilex ι β) :=
  { Pilex.partialOrder, Pi.commGroup with
    mul_le_mul_left := fun x y hxy z =>
      hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
        Or.inr
          ⟨i, fun j hji =>
            show z j * x j = z j * y j by
              rw [hi.1 j hji],
            mul_lt_mul_left' hi.2 _⟩ }

