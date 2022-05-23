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

This file defines the lexicographic order for Pi types. `a` is less than `b` if `a i = b i` for all
`i` up to some point `k`, and `a k < b k`.

## Notation

* `Πₗ i, α i`: Pi type equipped with the lexicographic order. Type synonym of `Π i, α i`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.sigma.order`: Lexicographic order on `Σₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σₗ' i, α i`.
* `data.prod.lex`: Lexicographic order on `α × β`.
-/


variable {ι : Type _} {β : ι → Type _} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

namespace Pi

instance {α : Type _} : ∀ [Inhabited α], Inhabited (Lex α) :=
  id

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
protected def Lex (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

-- mathport name: «exprΠₗ , »
notation3 "Πₗ " (...) ", " r:(scoped
  p =>/- This unfortunately results in a type that isn't delta-reduced, so we keep the notation out of the
    basic API, just in case -/
    Lex
    ∀ i, p i) =>
  r

@[simp]
theorem to_lex_apply (x : ∀ i, β i) (i : ι) : toLex x i = x i :=
  rfl

@[simp]
theorem of_lex_apply (x : Lex (∀ i, β i)) (i : ι) : ofLex x i = x i :=
  rfl

instance [LT ι] [∀ a, LT (β a)] : LT (Lex (∀ i, β i)) :=
  ⟨Pi.Lex (· < ·) fun _ => (· < ·)⟩

instance Lex.is_strict_order [LinearOrderₓ ι] [∀ a, PartialOrderₓ (β a)] : IsStrictOrder (Lex (∀ i, β i)) (· < ·) where
  irrefl := fun a ⟨k, hk₁, hk₂⟩ => lt_irreflₓ (a k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    rcases lt_trichotomyₓ N₁ N₂ with (H | rfl | H)
    exacts[⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
      ⟨N₂, fun j hj => (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]

instance [LinearOrderₓ ι] [∀ a, PartialOrderₓ (β a)] : PartialOrderₓ (Lex (∀ i, β i)) :=
  partialOrderOfSO (· < ·)

protected theorem Lex.is_strict_total_order' [LinearOrderₓ ι] (wf : WellFounded ((· < ·) : ι → ι → Prop))
    [∀ a, LinearOrderₓ (β a)] : IsStrictTotalOrder' (Lex (∀ i, β i)) (· < ·) :=
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

/-- `Πₗ i, α i` is a linear order if the original order is well-founded.
This cannot be an instance, since it depends on the well-foundedness of `<`. -/
protected noncomputable def Lex.linearOrder [LinearOrderₓ ι] (wf : WellFounded ((· < ·) : ι → ι → Prop))
    [∀ a, LinearOrderₓ (β a)] : LinearOrderₓ (Lex (∀ i, β i)) :=
  @linearOrderOfSTO' (Πₗ i, β i) (· < ·) (Pi.Lex.is_strict_total_order' wf) (Classical.decRel _)

theorem Lex.le_of_forall_le [LinearOrderₓ ι] (wf : WellFounded ((· < ·) : ι → ι → Prop)) [∀ a, LinearOrderₓ (β a)]
    {a b : Lex (∀ i, β i)} (h : ∀ i, a i ≤ b i) : a ≤ b := by
  let this : LinearOrderₓ (Πₗ i, β i) := lex.linear_order wf
  exact le_of_not_ltₓ fun ⟨i, hi⟩ => (h i).not_lt hi.2

--we might want the analog of `pi.ordered_cancel_comm_monoid` as well in the future
@[to_additive]
instance Lex.orderedCommGroup [LinearOrderₓ ι] [∀ a, OrderedCommGroup (β a)] : OrderedCommGroup (Lex (∀ i, β i)) :=
  { Pi.Lex.partialOrder, Pi.commGroup with
    mul_le_mul_left := fun x y hxy z =>
      hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
        Or.inr
          ⟨i, fun j hji =>
            show z j * x j = z j * y j by
              rw [hi.1 j hji],
            mul_lt_mul_left' hi.2 _⟩ }

end Pi

