/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu

! This file was ported from Lean 3 source module data.psigma.order
! leanprover-community/mathlib commit 198161d833f2c01498c39c266b0b3dbe2c7a8c07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sigma.Lex
import Mathbin.Order.BoundedOrder

/-!
# Lexicographic order on a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/815
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the lexicographic order on `Σₗ' i, α i`. `a` is less than `b` if its summand is
strictly less than the summand of `b` or they are in the same summand and `a` is less than `b`
there.

## Notation

* `Σₗ' i, α i`: Sigma type equipped with the lexicographic order. A type synonym of `Σ' i, α i`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.sigma.order`: Lexicographic order on `Σₗ i, α i`. Basically a twin of this file.
* `data.prod.lex`: Lexicographic order on `α × β`.

## TODO

Define the disjoint order on `Σ' i, α i`, where `x ≤ y` only if `x.fst = y.fst`.

Prove that a sigma type is a `no_max_order`, `no_min_order`, `densely_ordered` when its summands
are.
-/


variable {ι : Type _} {α : ι → Type _}

namespace PSigma

-- mathport name: «exprΣₗ' , »
notation3"Σₗ' "(...)", "r:(scoped p => Lex PSigma p) => r

namespace Lex

/-- The lexicographical `≤` on a sigma type. -/
instance hasLe [LT ι] [∀ i, LE (α i)] : LE (Σₗ' i, α i) :=
  ⟨Lex (· < ·) fun i => (· ≤ ·)⟩
#align psigma.lex.has_le PSigma.Lex.hasLe

/-- The lexicographical `<` on a sigma type. -/
instance hasLt [LT ι] [∀ i, LT (α i)] : LT (Σₗ' i, α i) :=
  ⟨Lex (· < ·) fun i => (· < ·)⟩
#align psigma.lex.has_lt PSigma.Lex.hasLt

instance preorder [Preorder ι] [∀ i, Preorder (α i)] : Preorder (Σₗ' i, α i) :=
  { Lex.hasLe, Lex.hasLt with 
    le_refl := fun ⟨i, a⟩ => Lex.right _ le_rfl
    le_trans := by 
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁r⟩ ⟨h₂r⟩
      · left
        apply lt_trans
        repeat' assumption
      · left
        assumption
      · left
        assumption
      · right
        apply le_trans
        repeat' assumption
    lt_iff_le_not_le := by
      refine' fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, _⟩, _⟩
      · rintro (⟨i, a, hji⟩ | ⟨i, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, hab⟩ := hab
        · exact hij.not_lt hji
        · exact lt_irrefl _ hji
        · exact lt_irrefl _ hij
        · exact hab.not_le hba
      · rintro ⟨⟨j, b, hij⟩ | ⟨i, hab⟩, hba⟩
        · exact lex.left _ _ hij
        · exact lex.right _ (hab.lt_of_not_le fun h => hba <| lex.right _ h) }
#align psigma.lex.preorder PSigma.Lex.preorder

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance partialOrder [PartialOrder ι] [∀ i, PartialOrder (α i)] : PartialOrder (Σₗ' i, α i) :=
  { Lex.preorder with
    le_antisymm := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, hlt₁⟩ | ⟨_, hlt₁⟩) (⟨_, _, hlt₂⟩ | ⟨_, hlt₂⟩)
      · exact (lt_irrefl a₁ <| hlt₁.trans hlt₂).elim
      · exact (lt_irrefl a₁ hlt₁).elim
      · exact (lt_irrefl a₁ hlt₂).elim
      · rw [hlt₁.antisymm hlt₂] }
#align psigma.lex.partial_order PSigma.Lex.partialOrder

/-- Dictionary / lexicographic linear_order for pairs. -/
instance linearOrder [LinearOrder ι] [∀ i, LinearOrder (α i)] : LinearOrder (Σₗ' i, α i) :=
  { Lex.partialOrder with
    le_total := by 
      rintro ⟨i, a⟩ ⟨j, b⟩
      obtain hij | rfl | hji := lt_trichotomy i j
      · exact Or.inl (lex.left _ _ hij)
      · obtain hab | hba := le_total a b
        · exact Or.inl (lex.right _ hab)
        · exact Or.inr (lex.right _ hba)
      · exact Or.inr (lex.left _ _ hji)
    DecidableEq := PSigma.decidableEq
    decidableLe := Lex.decidable _ _
    decidableLt := Lex.decidable _ _ }
#align psigma.lex.linear_order PSigma.Lex.linearOrder

/-- The lexicographical linear order on a sigma type. -/
instance orderBot [PartialOrder ι] [OrderBot ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σₗ' i, α i) where 
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by 
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact lex.right _ bot_le
    · exact lex.left _ _ ha
#align psigma.lex.order_bot PSigma.Lex.orderBot

/-- The lexicographical linear order on a sigma type. -/
instance orderTop [PartialOrder ι] [OrderTop ι] [∀ i, Preorder (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σₗ' i, α i) where 
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by 
    obtain rfl | ha := eq_top_or_lt_top a
    · exact lex.right _ le_top
    · exact lex.left _ _ ha
#align psigma.lex.order_top PSigma.Lex.orderTop

/-- The lexicographical linear order on a sigma type. -/
instance boundedOrder [PartialOrder ι] [BoundedOrder ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)]
    [OrderTop (α ⊤)] : BoundedOrder (Σₗ' i, α i) :=
  { Lex.orderBot, Lex.orderTop with }
#align psigma.lex.bounded_order PSigma.Lex.boundedOrder

instance densely_ordered [Preorder ι] [DenselyOrdered ι] [∀ i, Nonempty (α i)] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by 
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩
#align psigma.lex.densely_ordered PSigma.Lex.densely_ordered

instance densely_ordered_of_no_max_order [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMaxOrder (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by 
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩
#align psigma.lex.densely_ordered_of_no_max_order PSigma.Lex.densely_ordered_of_no_max_order

instance densely_ordered_of_no_min_order [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMinOrder (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by 
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩
#align psigma.lex.densely_ordered_of_no_min_order PSigma.Lex.densely_ordered_of_no_min_order

instance no_max_order_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMaxOrder ι]
    [∀ i, Nonempty (α i)] : NoMaxOrder (Σₗ' i, α i) :=
  ⟨by 
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩
#align psigma.lex.no_max_order_of_nonempty PSigma.Lex.no_max_order_of_nonempty

instance no_min_order_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMaxOrder ι]
    [∀ i, Nonempty (α i)] : NoMaxOrder (Σₗ' i, α i) :=
  ⟨by 
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩
#align psigma.lex.no_min_order_of_nonempty PSigma.Lex.no_min_order_of_nonempty

instance no_max_order [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMaxOrder (α i)] :
    NoMaxOrder (Σₗ' i, α i) :=
  ⟨by 
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩
#align psigma.lex.no_max_order PSigma.Lex.no_max_order

instance no_min_order [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMinOrder (α i)] :
    NoMinOrder (Σₗ' i, α i) :=
  ⟨by 
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩
#align psigma.lex.no_min_order PSigma.Lex.no_min_order

end Lex

end PSigma

