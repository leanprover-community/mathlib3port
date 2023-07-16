/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.locally_finite
! leanprover-community/mathlib commit 1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Preimage
import Mathbin.Data.Set.Intervals.UnorderedInterval

/-!
# Locally finite orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

Many theorems about these intervals can be found in `data.finset.locally_finite`.

## Examples

Naturally occurring locally finite orders are `ℕ`, `ℤ`, `ℕ+`, `fin n`, `α × β` the product of two
locally finite orders, `α →₀ β` the finitely supported functions to a locally finite order `β`...

## Main declarations

In a `locally_finite_order`,
* `finset.Icc`: Closed-closed interval as a finset.
* `finset.Ico`: Closed-open interval as a finset.
* `finset.Ioc`: Open-closed interval as a finset.
* `finset.Ioo`: Open-open interval as a finset.
* `finset.uIcc`: Unordered closed interval as a finset.
* `multiset.Icc`: Closed-closed interval as a multiset.
* `multiset.Ico`: Closed-open interval as a multiset.
* `multiset.Ioc`: Open-closed interval as a multiset.
* `multiset.Ioo`: Open-open interval as a multiset.

In a `locally_finite_order_top`,
* `finset.Ici`: Closed-infinite interval as a finset.
* `finset.Ioi`: Open-infinite interval as a finset.
* `multiset.Ici`: Closed-infinite interval as a multiset.
* `multiset.Ioi`: Open-infinite interval as a multiset.

In a `locally_finite_order_bot`,
* `finset.Iic`: Infinite-open interval as a finset.
* `finset.Iio`: Infinite-closed interval as a finset.
* `multiset.Iic`: Infinite-open interval as a multiset.
* `multiset.Iio`: Infinite-closed interval as a multiset.

## Instances

A `locally_finite_order` instance can be built
* for a subtype of a locally finite order. See `subtype.locally_finite_order`.
* for the product of two locally finite orders. See `prod.locally_finite_order`.
* for any fintype (but not as an instance). See `fintype.to_locally_finite_order`.
* from a definition of `finset.Icc` alone. See `locally_finite_order.of_Icc`.
* by pulling back `locally_finite_order β` through an order embedding `f : α →o β`. See
  `order_embedding.locally_finite_order`.

Instances for concrete types are proved in their respective files:
* `ℕ` is in `data.nat.interval`
* `ℤ` is in `data.int.interval`
* `ℕ+` is in `data.pnat.interval`
* `fin n` is in `data.fin.interval`
* `finset α` is in `data.finset.interval`
* `Σ i, α i` is in `data.sigma.interval`
Along, you will find lemmas about the cardinality of those finite intervals.

## TODO

Provide the `locally_finite_order` instance for `α ×ₗ β` where `locally_finite_order α` and
`fintype β`.

Provide the `locally_finite_order` instance for `α →₀ β` where `β` is locally finite. Provide the
`locally_finite_order` instance for `Π₀ i, β i` where all the `β i` are locally finite.

From `linear_order α`, `no_max_order α`, `locally_finite_order α`, we can also define an
order isomorphism `α ≃ ℕ` or `α ≃ ℤ`, depending on whether we have `order_bot α` or
`no_min_order α` and `nonempty α`. When `order_bot α`, we can match `a : α` to `(Iio a).card`.

We can provide `succ_order α` from `linear_order α` and `locally_finite_order α` using

```lean
lemma exists_min_greater [linear_order α] [locally_finite_order α] {x ub : α} (hx : x < ub) :
  ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y :=
begin -- very non golfed
  have h : (finset.Ioc x ub).nonempty := ⟨ub, finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩⟩,
  use finset.min' (finset.Ioc x ub) h,
  split,
  { have := finset.min'_mem _ h,
    simp * at * },
  rintro y hxy,
  obtain hy | hy := le_total y ub,
  apply finset.min'_le,
  simp * at *,
  exact (finset.min'_le _ _ (finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩)).trans hy,
end
```
Note that the converse is not true. Consider `{-2^z | z : ℤ} ∪ {2^z | z : ℤ}`. Any element has a
successor (and actually a predecessor as well), so it is a `succ_order`, but it's not locally finite
as `Icc (-1) 1` is infinite.
-/


open Finset Function

#print LocallyFiniteOrder /-
/-- A locally finite order is an order where bounded intervals are finite. When you don't care too
much about definitional equality, you can use `locally_finite_order.of_Icc` or
`locally_finite_order.of_finite_Icc` to build a locally finite order from just `finset.Icc`. -/
class LocallyFiniteOrder (α : Type _) [Preorder α] where
  finsetIcc : α → α → Finset α
  finsetIco : α → α → Finset α
  finsetIoc : α → α → Finset α
  finsetIoo : α → α → Finset α
  finset_mem_Icc : ∀ a b x : α, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b
  finset_mem_Ico : ∀ a b x : α, x ∈ finset_Ico a b ↔ a ≤ x ∧ x < b
  finset_mem_Ioc : ∀ a b x : α, x ∈ finset_Ioc a b ↔ a < x ∧ x ≤ b
  finset_mem_Ioo : ∀ a b x : α, x ∈ finset_Ioo a b ↔ a < x ∧ x < b
#align locally_finite_order LocallyFiniteOrder
-/

#print LocallyFiniteOrderTop /-
/-- A locally finite order top is an order where all intervals bounded above are finite. This is
slightly weaker than `locally_finite_order` + `order_top` as it allows empty types. -/
class LocallyFiniteOrderTop (α : Type _) [Preorder α] where
  finsetIoi : α → Finset α
  finsetIci : α → Finset α
  finset_mem_Ici : ∀ a x : α, x ∈ finset_Ici a ↔ a ≤ x
  finset_mem_Ioi : ∀ a x : α, x ∈ finset_Ioi a ↔ a < x
#align locally_finite_order_top LocallyFiniteOrderTop
-/

#print LocallyFiniteOrderBot /-
/-- A locally finite order bot is an order where all intervals bounded below are finite. This is
slightly weaker than `locally_finite_order` + `order_bot` as it allows empty types. -/
class LocallyFiniteOrderBot (α : Type _) [Preorder α] where
  finsetIio : α → Finset α
  finsetIic : α → Finset α
  finset_mem_Iic : ∀ a x : α, x ∈ finset_Iic a ↔ x ≤ a
  finset_mem_Iio : ∀ a x : α, x ∈ finset_Iio a ↔ x < a
#align locally_finite_order_bot LocallyFiniteOrderBot
-/

#print LocallyFiniteOrder.ofIcc' /-
/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrder.ofIcc' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Icc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) :
    LocallyFiniteOrder α :=
  { finsetIcc
    finsetIco := fun a b => (finset_Icc a b).filterₓ fun x => ¬b ≤ x
    finsetIoc := fun a b => (finset_Icc a b).filterₓ fun x => ¬x ≤ a
    finsetIoo := fun a b => (finset_Icc a b).filterₓ fun x => ¬x ≤ a ∧ ¬b ≤ x
    finset_mem_Icc := mem_Icc
    finset_mem_Ico := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_assoc', lt_iff_le_not_le]
    finset_mem_Ioc := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_not_le]
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_not_le, lt_iff_le_not_le] }
#align locally_finite_order.of_Icc' LocallyFiniteOrder.ofIcc'
-/

#print LocallyFiniteOrder.ofIcc /-
/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `partial_order` but only
`decidable_eq`. -/
def LocallyFiniteOrder.ofIcc (α : Type _) [PartialOrder α] [DecidableEq α]
    (finset_Icc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) :
    LocallyFiniteOrder α :=
  { finsetIcc
    finsetIco := fun a b => (finset_Icc a b).filterₓ fun x => x ≠ b
    finsetIoc := fun a b => (finset_Icc a b).filterₓ fun x => a ≠ x
    finsetIoo := fun a b => (finset_Icc a b).filterₓ fun x => a ≠ x ∧ x ≠ b
    finset_mem_Icc := mem_Icc
    finset_mem_Ico := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_assoc', lt_iff_le_and_ne]
    finset_mem_Ioc := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_and_ne]
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_and_ne, lt_iff_le_and_ne] }
#align locally_finite_order.of_Icc LocallyFiniteOrder.ofIcc
-/

#print LocallyFiniteOrderTop.ofIci' /-
/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrderTop.ofIci' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Ici : α → Finset α) (mem_Ici : ∀ a x, x ∈ finset_Ici a ↔ a ≤ x) :
    LocallyFiniteOrderTop α :=
  { finsetIci
    finsetIoi := fun a => (finset_Ici a).filterₓ fun x => ¬x ≤ a
    finset_mem_Ici := mem_Ici
    finset_mem_Ioi := fun a x => by rw [mem_filter, mem_Ici, lt_iff_le_not_le] }
#align locally_finite_order_top.of_Ici' LocallyFiniteOrderTop.ofIci'
-/

#print LocallyFiniteOrderTop.ofIci /-
/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici'`, this one requires `partial_order` but
only `decidable_eq`. -/
def LocallyFiniteOrderTop.ofIci (α : Type _) [PartialOrder α] [DecidableEq α]
    (finset_Ici : α → Finset α) (mem_Ici : ∀ a x, x ∈ finset_Ici a ↔ a ≤ x) :
    LocallyFiniteOrderTop α :=
  { finsetIci
    finsetIoi := fun a => (finset_Ici a).filterₓ fun x => a ≠ x
    finset_mem_Ici := mem_Ici
    finset_mem_Ioi := fun a x => by rw [mem_filter, mem_Ici, lt_iff_le_and_ne] }
#align locally_finite_order_top.of_Ici LocallyFiniteOrderTop.ofIci
-/

#print LocallyFiniteOrderBot.ofIic' /-
/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrderBot.ofIic' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Iic : α → Finset α) (mem_Iic : ∀ a x, x ∈ finset_Iic a ↔ x ≤ a) :
    LocallyFiniteOrderBot α :=
  { finsetIic
    finsetIio := fun a => (finset_Iic a).filterₓ fun x => ¬a ≤ x
    finset_mem_Iic := mem_Iic
    finset_mem_Iio := fun a x => by rw [mem_filter, mem_Iic, lt_iff_le_not_le] }
#align locally_finite_order_bot.of_Iic' LocallyFiniteOrderBot.ofIic'
-/

#print LocallyFiniteOrderTop.ofIic /-
/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici'`, this one requires `partial_order` but
only `decidable_eq`. -/
def LocallyFiniteOrderTop.ofIic (α : Type _) [PartialOrder α] [DecidableEq α]
    (finset_Iic : α → Finset α) (mem_Iic : ∀ a x, x ∈ finset_Iic a ↔ x ≤ a) :
    LocallyFiniteOrderBot α :=
  { finsetIic
    finsetIio := fun a => (finset_Iic a).filterₓ fun x => x ≠ a
    finset_mem_Iic := mem_Iic
    finset_mem_Iio := fun a x => by rw [mem_filter, mem_Iic, lt_iff_le_and_ne] }
#align locally_finite_order_top.of_Iic LocallyFiniteOrderTop.ofIic
-/

variable {α β : Type _}

#print IsEmpty.toLocallyFiniteOrder /-
-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[reducible]
protected def IsEmpty.toLocallyFiniteOrder [Preorder α] [IsEmpty α] : LocallyFiniteOrder α
    where
  finsetIcc := isEmptyElim
  finsetIco := isEmptyElim
  finsetIoc := isEmptyElim
  finsetIoo := isEmptyElim
  finset_mem_Icc := isEmptyElim
  finset_mem_Ico := isEmptyElim
  finset_mem_Ioc := isEmptyElim
  finset_mem_Ioo := isEmptyElim
#align is_empty.to_locally_finite_order IsEmpty.toLocallyFiniteOrder
-/

#print IsEmpty.toLocallyFiniteOrderTop /-
-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[reducible]
protected def IsEmpty.toLocallyFiniteOrderTop [Preorder α] [IsEmpty α] : LocallyFiniteOrderTop α
    where
  finsetIci := isEmptyElim
  finsetIoi := isEmptyElim
  finset_mem_Ici := isEmptyElim
  finset_mem_Ioi := isEmptyElim
#align is_empty.to_locally_finite_order_top IsEmpty.toLocallyFiniteOrderTop
-/

#print IsEmpty.toLocallyFiniteOrderBot /-
-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[reducible]
protected def IsEmpty.toLocallyFiniteOrderBot [Preorder α] [IsEmpty α] : LocallyFiniteOrderBot α
    where
  finsetIic := isEmptyElim
  finsetIio := isEmptyElim
  finset_mem_Iic := isEmptyElim
  finset_mem_Iio := isEmptyElim
#align is_empty.to_locally_finite_order_bot IsEmpty.toLocallyFiniteOrderBot
-/

/-! ### Intervals as finsets -/


namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b x : α}

#print Finset.Icc /-
/-- The finset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a finset.
-/
def Icc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIcc a b
#align finset.Icc Finset.Icc
-/

#print Finset.Ico /-
/-- The finset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a finset.
-/
def Ico (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIco a b
#align finset.Ico Finset.Ico
-/

#print Finset.Ioc /-
/-- The finset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a finset.
-/
def Ioc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoc a b
#align finset.Ioc Finset.Ioc
-/

#print Finset.Ioo /-
/-- The finset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a finset.
-/
def Ioo (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoo a b
#align finset.Ioo Finset.Ioo
-/

#print Finset.mem_Icc /-
@[simp]
theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Icc a b x
#align finset.mem_Icc Finset.mem_Icc
-/

#print Finset.mem_Ico /-
@[simp]
theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ico a b x
#align finset.mem_Ico Finset.mem_Ico
-/

#print Finset.mem_Ioc /-
@[simp]
theorem mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Ioc a b x
#align finset.mem_Ioc Finset.mem_Ioc
-/

#print Finset.mem_Ioo /-
@[simp]
theorem mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ioo a b x
#align finset.mem_Ioo Finset.mem_Ioo
-/

#print Finset.coe_Icc /-
@[simp, norm_cast]
theorem coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b :=
  Set.ext fun _ => mem_Icc
#align finset.coe_Icc Finset.coe_Icc
-/

#print Finset.coe_Ico /-
@[simp, norm_cast]
theorem coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b :=
  Set.ext fun _ => mem_Ico
#align finset.coe_Ico Finset.coe_Ico
-/

#print Finset.coe_Ioc /-
@[simp, norm_cast]
theorem coe_Ioc (a b : α) : (Ioc a b : Set α) = Set.Ioc a b :=
  Set.ext fun _ => mem_Ioc
#align finset.coe_Ioc Finset.coe_Ioc
-/

#print Finset.coe_Ioo /-
@[simp, norm_cast]
theorem coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b :=
  Set.ext fun _ => mem_Ioo
#align finset.coe_Ioo Finset.coe_Ioo
-/

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a x : α}

#print Finset.Ici /-
/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a finset. -/
def Ici (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIci a
#align finset.Ici Finset.Ici
-/

#print Finset.Ioi /-
/-- The finset of elements `x` such that `a < x`. Basically `set.Ioi a` as a finset. -/
def Ioi (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIoi a
#align finset.Ioi Finset.Ioi
-/

#print Finset.mem_Ici /-
@[simp]
theorem mem_Ici : x ∈ Ici a ↔ a ≤ x :=
  LocallyFiniteOrderTop.finset_mem_Ici _ _
#align finset.mem_Ici Finset.mem_Ici
-/

#print Finset.mem_Ioi /-
@[simp]
theorem mem_Ioi : x ∈ Ioi a ↔ a < x :=
  LocallyFiniteOrderTop.finset_mem_Ioi _ _
#align finset.mem_Ioi Finset.mem_Ioi
-/

#print Finset.coe_Ici /-
@[simp, norm_cast]
theorem coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a :=
  Set.ext fun _ => mem_Ici
#align finset.coe_Ici Finset.coe_Ici
-/

#print Finset.coe_Ioi /-
@[simp, norm_cast]
theorem coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a :=
  Set.ext fun _ => mem_Ioi
#align finset.coe_Ioi Finset.coe_Ioi
-/

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a x : α}

#print Finset.Iic /-
/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Iic a` as a finset. -/
def Iic (a : α) : Finset α :=
  LocallyFiniteOrderBot.finsetIic a
#align finset.Iic Finset.Iic
-/

#print Finset.Iio /-
/-- The finset of elements `x` such that `a < x`. Basically `set.Iio a` as a finset. -/
def Iio (a : α) : Finset α :=
  LocallyFiniteOrderBot.finsetIio a
#align finset.Iio Finset.Iio
-/

#print Finset.mem_Iic /-
@[simp]
theorem mem_Iic : x ∈ Iic a ↔ x ≤ a :=
  LocallyFiniteOrderBot.finset_mem_Iic _ _
#align finset.mem_Iic Finset.mem_Iic
-/

#print Finset.mem_Iio /-
@[simp]
theorem mem_Iio : x ∈ Iio a ↔ x < a :=
  LocallyFiniteOrderBot.finset_mem_Iio _ _
#align finset.mem_Iio Finset.mem_Iio
-/

#print Finset.coe_Iic /-
@[simp, norm_cast]
theorem coe_Iic (a : α) : (Iic a : Set α) = Set.Iic a :=
  Set.ext fun _ => mem_Iic
#align finset.coe_Iic Finset.coe_Iic
-/

#print Finset.coe_Iio /-
@[simp, norm_cast]
theorem coe_Iio (a : α) : (Iio a : Set α) = Set.Iio a :=
  Set.ext fun _ => mem_Iio
#align finset.coe_Iio Finset.coe_Iio
-/

end LocallyFiniteOrderBot

section OrderTop

variable [LocallyFiniteOrder α] [OrderTop α] {a x : α}

#print LocallyFiniteOrder.toLocallyFiniteOrderTop /-
-- See note [lower priority instance]
instance (priority := 100) LocallyFiniteOrder.toLocallyFiniteOrderTop : LocallyFiniteOrderTop α
    where
  finsetIci b := Icc b ⊤
  finsetIoi b := Ioc b ⊤
  finset_mem_Ici a x := by rw [mem_Icc, and_iff_left le_top]
  finset_mem_Ioi a x := by rw [mem_Ioc, and_iff_left le_top]
#align locally_finite_order.to_locally_finite_order_top LocallyFiniteOrder.toLocallyFiniteOrderTop
-/

#print Finset.Ici_eq_Icc /-
theorem Ici_eq_Icc (a : α) : Ici a = Icc a ⊤ :=
  rfl
#align finset.Ici_eq_Icc Finset.Ici_eq_Icc
-/

#print Finset.Ioi_eq_Ioc /-
theorem Ioi_eq_Ioc (a : α) : Ioi a = Ioc a ⊤ :=
  rfl
#align finset.Ioi_eq_Ioc Finset.Ioi_eq_Ioc
-/

end OrderTop

section OrderBot

variable [OrderBot α] [LocallyFiniteOrder α] {b x : α}

#print Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot /-
-- See note [lower priority instance]
instance (priority := 100) LocallyFiniteOrder.toLocallyFiniteOrderBot : LocallyFiniteOrderBot α
    where
  finsetIic := Icc ⊥
  finsetIio := Ico ⊥
  finset_mem_Iic a x := by rw [mem_Icc, and_iff_right bot_le]
  finset_mem_Iio a x := by rw [mem_Ico, and_iff_right bot_le]
#align finset.locally_finite_order.to_locally_finite_order_bot Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot
-/

#print Finset.Iic_eq_Icc /-
theorem Iic_eq_Icc : Iic = Icc (⊥ : α) :=
  rfl
#align finset.Iic_eq_Icc Finset.Iic_eq_Icc
-/

#print Finset.Iio_eq_Ico /-
theorem Iio_eq_Ico : Iio = Ico (⊥ : α) :=
  rfl
#align finset.Iio_eq_Ico Finset.Iio_eq_Ico
-/

end OrderBot

end Preorder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a b x : α}

#print Finset.uIcc /-
/-- `finset.uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `finset.Icc (a ⊓ b) (a ⊔ b)`. In a
product type, `finset.uIcc` corresponds to the bounding box of the two elements. -/
def uIcc (a b : α) : Finset α :=
  Icc (a ⊓ b) (a ⊔ b)
#align finset.uIcc Finset.uIcc
-/

scoped[FinsetInterval] notation "[" a ", " b "]" => Finset.uIcc a b

#print Finset.mem_uIcc /-
@[simp]
theorem mem_uIcc : x ∈ uIcc a b ↔ a ⊓ b ≤ x ∧ x ≤ a ⊔ b :=
  mem_Icc
#align finset.mem_uIcc Finset.mem_uIcc
-/

#print Finset.coe_uIcc /-
@[simp, norm_cast]
theorem coe_uIcc (a b : α) : ([a, b] : Set α) = Set.uIcc a b :=
  coe_Icc _ _
#align finset.coe_uIcc Finset.coe_uIcc
-/

end Lattice

end Finset

/-! ### Intervals as multisets -/


namespace Multiset

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

#print Multiset.Icc /-
/-- The multiset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a
multiset. -/
def Icc (a b : α) : Multiset α :=
  (Finset.Icc a b).val
#align multiset.Icc Multiset.Icc
-/

#print Multiset.Ico /-
/-- The multiset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a
multiset. -/
def Ico (a b : α) : Multiset α :=
  (Finset.Ico a b).val
#align multiset.Ico Multiset.Ico
-/

#print Multiset.Ioc /-
/-- The multiset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a
multiset. -/
def Ioc (a b : α) : Multiset α :=
  (Finset.Ioc a b).val
#align multiset.Ioc Multiset.Ioc
-/

#print Multiset.Ioo /-
/-- The multiset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a
multiset. -/
def Ioo (a b : α) : Multiset α :=
  (Finset.Ioo a b).val
#align multiset.Ioo Multiset.Ioo
-/

#print Multiset.mem_Icc /-
@[simp]
theorem mem_Icc {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := by
  rw [Icc, ← Finset.mem_def, Finset.mem_Icc]
#align multiset.mem_Icc Multiset.mem_Icc
-/

#print Multiset.mem_Ico /-
@[simp]
theorem mem_Ico {a b x : α} : x ∈ Ico a b ↔ a ≤ x ∧ x < b := by
  rw [Ico, ← Finset.mem_def, Finset.mem_Ico]
#align multiset.mem_Ico Multiset.mem_Ico
-/

#print Multiset.mem_Ioc /-
@[simp]
theorem mem_Ioc {a b x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := by
  rw [Ioc, ← Finset.mem_def, Finset.mem_Ioc]
#align multiset.mem_Ioc Multiset.mem_Ioc
-/

#print Multiset.mem_Ioo /-
@[simp]
theorem mem_Ioo {a b x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b := by
  rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]
#align multiset.mem_Ioo Multiset.mem_Ioo
-/

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

#print Multiset.Ici /-
/-- The multiset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a multiset. -/
def Ici (a : α) : Multiset α :=
  (Finset.Ici a).val
#align multiset.Ici Multiset.Ici
-/

#print Multiset.Ioi /-
/-- The multiset of elements `x` such that `a < x`. Basically `set.Ioi a` as a multiset. -/
def Ioi (a : α) : Multiset α :=
  (Finset.Ioi a).val
#align multiset.Ioi Multiset.Ioi
-/

#print Multiset.mem_Ici /-
@[simp]
theorem mem_Ici {a x : α} : x ∈ Ici a ↔ a ≤ x := by rw [Ici, ← Finset.mem_def, Finset.mem_Ici]
#align multiset.mem_Ici Multiset.mem_Ici
-/

#print Multiset.mem_Ioi /-
@[simp]
theorem mem_Ioi {a x : α} : x ∈ Ioi a ↔ a < x := by rw [Ioi, ← Finset.mem_def, Finset.mem_Ioi]
#align multiset.mem_Ioi Multiset.mem_Ioi
-/

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

#print Multiset.Iic /-
/-- The multiset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a multiset. -/
def Iic (b : α) : Multiset α :=
  (Finset.Iic b).val
#align multiset.Iic Multiset.Iic
-/

#print Multiset.Iio /-
/-- The multiset of elements `x` such that `x < b`. Basically `set.Iio b` as a multiset. -/
def Iio (b : α) : Multiset α :=
  (Finset.Iio b).val
#align multiset.Iio Multiset.Iio
-/

#print Multiset.mem_Iic /-
@[simp]
theorem mem_Iic {b x : α} : x ∈ Iic b ↔ x ≤ b := by rw [Iic, ← Finset.mem_def, Finset.mem_Iic]
#align multiset.mem_Iic Multiset.mem_Iic
-/

#print Multiset.mem_Iio /-
@[simp]
theorem mem_Iio {b x : α} : x ∈ Iio b ↔ x < b := by rw [Iio, ← Finset.mem_def, Finset.mem_Iio]
#align multiset.mem_Iio Multiset.mem_Iio
-/

end LocallyFiniteOrderBot

end Multiset

/-! ### Finiteness of `set` intervals -/


namespace Set

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] (a b : α)

#print Set.fintypeIcc /-
instance fintypeIcc : Fintype (Icc a b) :=
  Fintype.ofFinset (Finset.Icc a b) fun x => Finset.mem_Icc
#align set.fintype_Icc Set.fintypeIcc
-/

#print Set.fintypeIco /-
instance fintypeIco : Fintype (Ico a b) :=
  Fintype.ofFinset (Finset.Ico a b) fun x => Finset.mem_Ico
#align set.fintype_Ico Set.fintypeIco
-/

#print Set.fintypeIoc /-
instance fintypeIoc : Fintype (Ioc a b) :=
  Fintype.ofFinset (Finset.Ioc a b) fun x => Finset.mem_Ioc
#align set.fintype_Ioc Set.fintypeIoc
-/

#print Set.fintypeIoo /-
instance fintypeIoo : Fintype (Ioo a b) :=
  Fintype.ofFinset (Finset.Ioo a b) fun x => Finset.mem_Ioo
#align set.fintype_Ioo Set.fintypeIoo
-/

#print Set.finite_Icc /-
theorem finite_Icc : (Icc a b).Finite :=
  (Icc a b).toFinite
#align set.finite_Icc Set.finite_Icc
-/

#print Set.finite_Ico /-
theorem finite_Ico : (Ico a b).Finite :=
  (Ico a b).toFinite
#align set.finite_Ico Set.finite_Ico
-/

#print Set.finite_Ioc /-
theorem finite_Ioc : (Ioc a b).Finite :=
  (Ioc a b).toFinite
#align set.finite_Ioc Set.finite_Ioc
-/

#print Set.finite_Ioo /-
theorem finite_Ioo : (Ioo a b).Finite :=
  (Ioo a b).toFinite
#align set.finite_Ioo Set.finite_Ioo
-/

end Preorder

section OrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] (a : α)

#print Set.fintypeIci /-
instance fintypeIci : Fintype (Ici a) :=
  Fintype.ofFinset (Finset.Ici a) fun x => Finset.mem_Ici
#align set.fintype_Ici Set.fintypeIci
-/

#print Set.fintypeIoi /-
instance fintypeIoi : Fintype (Ioi a) :=
  Fintype.ofFinset (Finset.Ioi a) fun x => Finset.mem_Ioi
#align set.fintype_Ioi Set.fintypeIoi
-/

#print Set.finite_Ici /-
theorem finite_Ici : (Ici a).Finite :=
  (Ici a).toFinite
#align set.finite_Ici Set.finite_Ici
-/

#print Set.finite_Ioi /-
theorem finite_Ioi : (Ioi a).Finite :=
  (Ioi a).toFinite
#align set.finite_Ioi Set.finite_Ioi
-/

end OrderTop

section OrderBot

variable [Preorder α] [LocallyFiniteOrderBot α] (b : α)

#print Set.fintypeIic /-
instance fintypeIic : Fintype (Iic b) :=
  Fintype.ofFinset (Finset.Iic b) fun x => Finset.mem_Iic
#align set.fintype_Iic Set.fintypeIic
-/

#print Set.fintypeIio /-
instance fintypeIio : Fintype (Iio b) :=
  Fintype.ofFinset (Finset.Iio b) fun x => Finset.mem_Iio
#align set.fintype_Iio Set.fintypeIio
-/

#print Set.finite_Iic /-
theorem finite_Iic : (Iic b).Finite :=
  (Iic b).toFinite
#align set.finite_Iic Set.finite_Iic
-/

#print Set.finite_Iio /-
theorem finite_Iio : (Iio b).Finite :=
  (Iio b).toFinite
#align set.finite_Iio Set.finite_Iio
-/

end OrderBot

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] (a b : α)

instance fintypeUIcc : Fintype (uIcc a b) :=
  Fintype.ofFinset (Finset.uIcc a b) fun x => Finset.mem_uIcc
#align set.fintype_uIcc Set.fintypeUIcc

@[simp]
theorem finite_interval : (uIcc a b).Finite :=
  (uIcc _ _).toFinite
#align set.finite_interval Set.finite_interval

end Lattice

end Set

/-! ### Instances -/


open Finset

section Preorder

variable [Preorder α] [Preorder β]

#print LocallyFiniteOrder.ofFiniteIcc /-
/-- A noncomputable constructor from the finiteness of all closed intervals. -/
noncomputable def LocallyFiniteOrder.ofFiniteIcc (h : ∀ a b : α, (Set.Icc a b).Finite) :
    LocallyFiniteOrder α :=
  @LocallyFiniteOrder.ofIcc' α _ (Classical.decRel _) (fun a b => (h a b).toFinset) fun a b x => by
    rw [Set.Finite.mem_toFinset, Set.mem_Icc]
#align locally_finite_order.of_finite_Icc LocallyFiniteOrder.ofFiniteIcc
-/

#print Fintype.toLocallyFiniteOrder /-
/-- A fintype is a locally finite order.

This is not an instance as it would not be defeq to better instances such as
`fin.locally_finite_order`.
-/
@[reducible]
def Fintype.toLocallyFiniteOrder [Fintype α] [@DecidableRel α (· < ·)] [@DecidableRel α (· ≤ ·)] :
    LocallyFiniteOrder α where
  finsetIcc a b := (Set.Icc a b).toFinset
  finsetIco a b := (Set.Ico a b).toFinset
  finsetIoc a b := (Set.Ioc a b).toFinset
  finsetIoo a b := (Set.Ioo a b).toFinset
  finset_mem_Icc a b x := by simp only [Set.mem_toFinset, Set.mem_Icc]
  finset_mem_Ico a b x := by simp only [Set.mem_toFinset, Set.mem_Ico]
  finset_mem_Ioc a b x := by simp only [Set.mem_toFinset, Set.mem_Ioc]
  finset_mem_Ioo a b x := by simp only [Set.mem_toFinset, Set.mem_Ioo]
#align fintype.to_locally_finite_order Fintype.toLocallyFiniteOrder
-/

instance : Subsingleton (LocallyFiniteOrder α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIcc : h₀_finset_Icc = h₁_finset_Icc := by ext a b x;
      rw [h₀_finset_mem_Icc, h₁_finset_mem_Icc]
    have hIco : h₀_finset_Ico = h₁_finset_Ico := by ext a b x;
      rw [h₀_finset_mem_Ico, h₁_finset_mem_Ico]
    have hIoc : h₀_finset_Ioc = h₁_finset_Ioc := by ext a b x;
      rw [h₀_finset_mem_Ioc, h₁_finset_mem_Ioc]
    have hIoo : h₀_finset_Ioo = h₁_finset_Ioo := by ext a b x;
      rw [h₀_finset_mem_Ioo, h₁_finset_mem_Ioo]
    simp_rw [hIcc, hIco, hIoc, hIoo]

instance : Subsingleton (LocallyFiniteOrderTop α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIci : h₀_finset_Ici = h₁_finset_Ici := by ext a b x;
      rw [h₀_finset_mem_Ici, h₁_finset_mem_Ici]
    have hIoi : h₀_finset_Ioi = h₁_finset_Ioi := by ext a b x;
      rw [h₀_finset_mem_Ioi, h₁_finset_mem_Ioi]
    simp_rw [hIci, hIoi]

instance : Subsingleton (LocallyFiniteOrderBot α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIic : h₀_finset_Iic = h₁_finset_Iic := by ext a b x;
      rw [h₀_finset_mem_Iic, h₁_finset_mem_Iic]
    have hIio : h₀_finset_Iio = h₁_finset_Iio := by ext a b x;
      rw [h₀_finset_mem_Iio, h₁_finset_mem_Iio]
    simp_rw [hIic, hIio]

#print OrderEmbedding.locallyFiniteOrder /-
-- Should this be called `locally_finite_order.lift`?
/-- Given an order embedding `α ↪o β`, pulls back the `locally_finite_order` on `β` to `α`. -/
protected noncomputable def OrderEmbedding.locallyFiniteOrder [LocallyFiniteOrder β] (f : α ↪o β) :
    LocallyFiniteOrder α
    where
  finsetIcc a b := (Icc (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIco a b := (Ico (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIoc a b := (Ioc (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIoo a b := (Ioo (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finset_mem_Icc a b x := by rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le]
  finset_mem_Ico a b x := by rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt]
  finset_mem_Ioc a b x := by rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le]
  finset_mem_Ioo a b x := by rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt]
#align order_embedding.locally_finite_order OrderEmbedding.locallyFiniteOrder
-/

open OrderDual

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : α)

/-- Note we define `Icc (to_dual a) (to_dual b)` as `Icc α _ _ b a` (which has type `finset α` not
`finset αᵒᵈ`!) instead of `(Icc b a).map to_dual.to_embedding` as this means the
following is defeq:
```
lemma this : (Icc (to_dual (to_dual a)) (to_dual (to_dual b)) : _) = (Icc a b : _) := rfl
```
-/
instance : LocallyFiniteOrder αᵒᵈ
    where
  finsetIcc a b := @Icc α _ _ (ofDual b) (ofDual a)
  finsetIco a b := @Ioc α _ _ (ofDual b) (ofDual a)
  finsetIoc a b := @Ico α _ _ (ofDual b) (ofDual a)
  finsetIoo a b := @Ioo α _ _ (ofDual b) (ofDual a)
  finset_mem_Icc a b x := mem_Icc.trans (and_comm' _ _)
  finset_mem_Ico a b x := mem_Ioc.trans (and_comm' _ _)
  finset_mem_Ioc a b x := mem_Ico.trans (and_comm' _ _)
  finset_mem_Ioo a b x := mem_Ioo.trans (and_comm' _ _)

#print Icc_toDual /-
theorem Icc_toDual : Icc (toDual a) (toDual b) = (Icc b a).map toDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm; ext c; rw [mem_Icc, mem_Icc]; exact and_comm' _ _
#align Icc_to_dual Icc_toDual
-/

#print Ico_toDual /-
theorem Ico_toDual : Ico (toDual a) (toDual b) = (Ioc b a).map toDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm; ext c; rw [mem_Ico, mem_Ioc]; exact and_comm' _ _
#align Ico_to_dual Ico_toDual
-/

#print Ioc_toDual /-
theorem Ioc_toDual : Ioc (toDual a) (toDual b) = (Ico b a).map toDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm; ext c; rw [mem_Ioc, mem_Ico]; exact and_comm' _ _
#align Ioc_to_dual Ioc_toDual
-/

#print Ioo_toDual /-
theorem Ioo_toDual : Ioo (toDual a) (toDual b) = (Ioo b a).map toDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm; ext c; rw [mem_Ioo, mem_Ioo]; exact and_comm' _ _
#align Ioo_to_dual Ioo_toDual
-/

#print Icc_ofDual /-
theorem Icc_ofDual (a b : αᵒᵈ) : Icc (ofDual a) (ofDual b) = (Icc b a).map ofDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm; ext c; rw [mem_Icc, mem_Icc]; exact and_comm' _ _
#align Icc_of_dual Icc_ofDual
-/

#print Ico_ofDual /-
theorem Ico_ofDual (a b : αᵒᵈ) : Ico (ofDual a) (ofDual b) = (Ioc b a).map ofDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm; ext c; rw [mem_Ico, mem_Ioc]; exact and_comm' _ _
#align Ico_of_dual Ico_ofDual
-/

#print Ioc_ofDual /-
theorem Ioc_ofDual (a b : αᵒᵈ) : Ioc (ofDual a) (ofDual b) = (Ico b a).map ofDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm; ext c; rw [mem_Ioc, mem_Ico]; exact and_comm' _ _
#align Ioc_of_dual Ioc_ofDual
-/

#print Ioo_ofDual /-
theorem Ioo_ofDual (a b : αᵒᵈ) : Ioo (ofDual a) (ofDual b) = (Ioo b a).map ofDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm; ext c; rw [mem_Ioo, mem_Ioo]; exact and_comm' _ _
#align Ioo_of_dual Ioo_ofDual
-/

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

/-- Note we define `Iic (to_dual a)` as `Ici a` (which has type `finset α` not `finset αᵒᵈ`!)
instead of `(Ici a).map to_dual.to_embedding` as this means the following is defeq:
```
lemma this : (Iic (to_dual (to_dual a)) : _) = (Iic a : _) := rfl
```
-/
instance : LocallyFiniteOrderBot αᵒᵈ
    where
  finsetIic a := @Ici α _ _ (ofDual a)
  finsetIio a := @Ioi α _ _ (ofDual a)
  finset_mem_Iic a x := mem_Ici
  finset_mem_Iio a x := mem_Ioi

#print Iic_toDual /-
theorem Iic_toDual (a : α) : Iic (toDual a) = (Ici a).map toDual.toEmbedding :=
  map_refl.symm
#align Iic_to_dual Iic_toDual
-/

#print Iio_toDual /-
theorem Iio_toDual (a : α) : Iio (toDual a) = (Ioi a).map toDual.toEmbedding :=
  map_refl.symm
#align Iio_to_dual Iio_toDual
-/

#print Ici_ofDual /-
theorem Ici_ofDual (a : αᵒᵈ) : Ici (ofDual a) = (Iic a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ici_of_dual Ici_ofDual
-/

#print Ioi_ofDual /-
theorem Ioi_ofDual (a : αᵒᵈ) : Ioi (ofDual a) = (Iio a).map ofDual.toEmbedding :=
  map_refl.symm
#align Ioi_of_dual Ioi_ofDual
-/

end LocallyFiniteOrderTop

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderBot α]

/-- Note we define `Ici (to_dual a)` as `Iic a` (which has type `finset α` not `finset αᵒᵈ`!)
instead of `(Iic a).map to_dual.to_embedding` as this means the following is defeq:
```
lemma this : (Ici (to_dual (to_dual a)) : _) = (Ici a : _) := rfl
```
-/
instance : LocallyFiniteOrderTop αᵒᵈ
    where
  finsetIci a := @Iic α _ _ (ofDual a)
  finsetIoi a := @Iio α _ _ (ofDual a)
  finset_mem_Ici a x := mem_Iic
  finset_mem_Ioi a x := mem_Iio

#print Ici_toDual /-
theorem Ici_toDual (a : α) : Ici (toDual a) = (Iic a).map toDual.toEmbedding :=
  map_refl.symm
#align Ici_to_dual Ici_toDual
-/

#print Ioi_toDual /-
theorem Ioi_toDual (a : α) : Ioi (toDual a) = (Iio a).map toDual.toEmbedding :=
  map_refl.symm
#align Ioi_to_dual Ioi_toDual
-/

#print Iic_ofDual /-
theorem Iic_ofDual (a : αᵒᵈ) : Iic (ofDual a) = (Ici a).map ofDual.toEmbedding :=
  map_refl.symm
#align Iic_of_dual Iic_ofDual
-/

#print Iio_ofDual /-
theorem Iio_ofDual (a : αᵒᵈ) : Iio (ofDual a) = (Ioi a).map ofDual.toEmbedding :=
  map_refl.symm
#align Iio_of_dual Iio_ofDual
-/

end LocallyFiniteOrderTop

namespace Prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrder (α × β) :=
  LocallyFiniteOrder.ofIcc' (α × β) (fun a b => Icc a.fst b.fst ×ˢ Icc a.snd b.snd) fun a b x => by
    rw [mem_product, mem_Icc, mem_Icc, and_and_and_comm]; rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrderTop (α × β) :=
  LocallyFiniteOrderTop.ofIci' (α × β) (fun a => Ici a.fst ×ˢ Ici a.snd) fun a x => by
    rw [mem_product, mem_Ici, mem_Ici]; rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] : LocallyFiniteOrderBot (α × β) :=
  LocallyFiniteOrderBot.ofIic' (α × β) (fun a => Iic a.fst ×ˢ Iic a.snd) fun a x => by
    rw [mem_product, mem_Iic, mem_Iic]; rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Prod.Icc_eq /-
theorem Icc_eq [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    Finset.Icc p q = Finset.Icc p.1 q.1 ×ˢ Finset.Icc p.2 q.2 :=
  rfl
#align prod.Icc_eq Prod.Icc_eq
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Prod.Icc_mk_mk /-
@[simp]
theorem Icc_mk_mk [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (a₁ a₂ : α) (b₁ b₂ : β) :
    Finset.Icc (a₁, b₁) (a₂, b₂) = Finset.Icc a₁ a₂ ×ˢ Finset.Icc b₁ b₂ :=
  rfl
#align prod.Icc_mk_mk Prod.Icc_mk_mk
-/

#print Prod.card_Icc /-
theorem card_Icc [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    (Finset.Icc p q).card = (Finset.Icc p.1 q.1).card * (Finset.Icc p.2 q.2).card :=
  Finset.card_product _ _
#align prod.card_Icc Prod.card_Icc
-/

end Prod

end Preorder

namespace Prod

variable [Lattice α] [Lattice β]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Prod.uIcc_eq /-
theorem uIcc_eq [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    Finset.uIcc p q = Finset.uIcc p.1 q.1 ×ˢ Finset.uIcc p.2 q.2 :=
  rfl
#align prod.uIcc_eq Prod.uIcc_eq
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Prod.uIcc_mk_mk /-
@[simp]
theorem uIcc_mk_mk [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (a₁ a₂ : α) (b₁ b₂ : β) :
    Finset.uIcc (a₁, b₁) (a₂, b₂) = Finset.uIcc a₁ a₂ ×ˢ Finset.uIcc b₁ b₂ :=
  rfl
#align prod.uIcc_mk_mk Prod.uIcc_mk_mk
-/

#print Prod.card_uIcc /-
theorem card_uIcc [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] (p q : α × β) :
    (Finset.uIcc p q).card = (Finset.uIcc p.1 q.1).card * (Finset.uIcc p.2 q.2).card :=
  Prod.card_Icc _ _
#align prod.card_uIcc Prod.card_uIcc
-/

end Prod

/-!
#### `with_top`, `with_bot`

Adding a `⊤` to a locally finite `order_top` keeps it locally finite.
Adding a `⊥` to a locally finite `order_bot` keeps it locally finite.
-/


namespace WithTop

variable (α) [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α]

attribute [local match_pattern] coe

attribute [local simp] Option.mem_iff

instance : LocallyFiniteOrder (WithTop α)
    where
  finsetIcc a b :=
    match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insertNone (Ici a)
    | (a : α), (b : α) => (Icc a b).map Embedding.some
  finsetIco a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ici a).map Embedding.some
    | (a : α), (b : α) => (Ico a b).map Embedding.some
  finsetIoc a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => insertNone (Ioi a)
    | (a : α), (b : α) => (Ioc a b).map Embedding.some
  finsetIoo a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ioi a).map Embedding.some
    | (a : α), (b : α) => (Ioo a b).map Embedding.some
  finset_mem_Icc a b x :=
    match a, b, x with
    | ⊤, ⊤, x => mem_singleton.trans (le_antisymm_iff.trans <| and_comm' _ _)
    | ⊤, (b : α), x =>
      iff_of_false (not_mem_empty _) fun h => (h.1.trans h.2).not_lt <| coe_lt_top _
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match1]
    | (a : α), ⊤, (x : α) => by simp [WithTop.LocallyFiniteOrder._match1, coe_eq_coe]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match1]
    | (a : α), (b : α), (x : α) => by simp [WithTop.LocallyFiniteOrder._match1, coe_eq_coe]
  finset_mem_Ico a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans_lt h.2
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match2]
    | (a : α), ⊤, (x : α) => by simp [WithTop.LocallyFiniteOrder._match2, coe_eq_coe, coe_lt_top]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match2]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match2, coe_eq_coe, coe_lt_coe]
  finset_mem_Ioc a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans_le h.2
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match3, coe_lt_top]
    | (a : α), ⊤, (x : α) => by simp [WithTop.LocallyFiniteOrder._match3, coe_eq_coe, coe_lt_coe]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match3]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match3, coe_eq_coe, coe_lt_coe]
  finset_mem_Ioo a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans h.2
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match4, coe_lt_top]
    | (a : α), ⊤, (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match4, coe_eq_coe, coe_lt_coe, coe_lt_top]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match4]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match4, coe_eq_coe, coe_lt_coe]

variable (a b : α)

#print WithTop.Icc_coe_top /-
theorem Icc_coe_top : Icc (a : WithTop α) ⊤ = insertNone (Ici a) :=
  rfl
#align with_top.Icc_coe_top WithTop.Icc_coe_top
-/

#print WithTop.Icc_coe_coe /-
theorem Icc_coe_coe : Icc (a : WithTop α) b = (Icc a b).map Embedding.some :=
  rfl
#align with_top.Icc_coe_coe WithTop.Icc_coe_coe
-/

#print WithTop.Ico_coe_top /-
theorem Ico_coe_top : Ico (a : WithTop α) ⊤ = (Ici a).map Embedding.some :=
  rfl
#align with_top.Ico_coe_top WithTop.Ico_coe_top
-/

#print WithTop.Ico_coe_coe /-
theorem Ico_coe_coe : Ico (a : WithTop α) b = (Ico a b).map Embedding.some :=
  rfl
#align with_top.Ico_coe_coe WithTop.Ico_coe_coe
-/

#print WithTop.Ioc_coe_top /-
theorem Ioc_coe_top : Ioc (a : WithTop α) ⊤ = insertNone (Ioi a) :=
  rfl
#align with_top.Ioc_coe_top WithTop.Ioc_coe_top
-/

#print WithTop.Ioc_coe_coe /-
theorem Ioc_coe_coe : Ioc (a : WithTop α) b = (Ioc a b).map Embedding.some :=
  rfl
#align with_top.Ioc_coe_coe WithTop.Ioc_coe_coe
-/

#print WithTop.Ioo_coe_top /-
theorem Ioo_coe_top : Ioo (a : WithTop α) ⊤ = (Ioi a).map Embedding.some :=
  rfl
#align with_top.Ioo_coe_top WithTop.Ioo_coe_top
-/

#print WithTop.Ioo_coe_coe /-
theorem Ioo_coe_coe : Ioo (a : WithTop α) b = (Ioo a b).map Embedding.some :=
  rfl
#align with_top.Ioo_coe_coe WithTop.Ioo_coe_coe
-/

end WithTop

namespace WithBot

variable (α) [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α]

instance : LocallyFiniteOrder (WithBot α) :=
  @OrderDual.locallyFiniteOrder (WithTop αᵒᵈ) _ _

variable (a b : α)

#print WithBot.Icc_bot_coe /-
theorem Icc_bot_coe : Icc (⊥ : WithBot α) b = insertNone (Iic b) :=
  rfl
#align with_bot.Icc_bot_coe WithBot.Icc_bot_coe
-/

#print WithBot.Icc_coe_coe /-
theorem Icc_coe_coe : Icc (a : WithBot α) b = (Icc a b).map Embedding.some :=
  rfl
#align with_bot.Icc_coe_coe WithBot.Icc_coe_coe
-/

#print WithBot.Ico_bot_coe /-
theorem Ico_bot_coe : Ico (⊥ : WithBot α) b = insertNone (Iio b) :=
  rfl
#align with_bot.Ico_bot_coe WithBot.Ico_bot_coe
-/

#print WithBot.Ico_coe_coe /-
theorem Ico_coe_coe : Ico (a : WithBot α) b = (Ico a b).map Embedding.some :=
  rfl
#align with_bot.Ico_coe_coe WithBot.Ico_coe_coe
-/

#print WithBot.Ioc_bot_coe /-
theorem Ioc_bot_coe : Ioc (⊥ : WithBot α) b = (Iic b).map Embedding.some :=
  rfl
#align with_bot.Ioc_bot_coe WithBot.Ioc_bot_coe
-/

#print WithBot.Ioc_coe_coe /-
theorem Ioc_coe_coe : Ioc (a : WithBot α) b = (Ioc a b).map Embedding.some :=
  rfl
#align with_bot.Ioc_coe_coe WithBot.Ioc_coe_coe
-/

#print WithBot.Ioo_bot_coe /-
theorem Ioo_bot_coe : Ioo (⊥ : WithBot α) b = (Iio b).map Embedding.some :=
  rfl
#align with_bot.Ioo_bot_coe WithBot.Ioo_bot_coe
-/

#print WithBot.Ioo_coe_coe /-
theorem Ioo_coe_coe : Ioo (a : WithBot α) b = (Ioo a b).map Embedding.some :=
  rfl
#align with_bot.Ioo_coe_coe WithBot.Ioo_coe_coe
-/

end WithBot

namespace OrderIso

variable [Preorder α] [Preorder β]

/-! #### Transfer locally finite orders across order isomorphisms -/


#print OrderIso.locallyFiniteOrder /-
-- See note [reducible non-instances]
/-- Transfer `locally_finite_order` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrder [LocallyFiniteOrder β] (f : α ≃o β) : LocallyFiniteOrder α
    where
  finsetIcc a b := (Icc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIco a b := (Ico (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoc a b := (Ioc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoo a b := (Ioo (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp
#align order_iso.locally_finite_order OrderIso.locallyFiniteOrder
-/

#print OrderIso.locallyFiniteOrderTop /-
-- See note [reducible non-instances]
/-- Transfer `locally_finite_order_top` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrderTop [LocallyFiniteOrderTop β] (f : α ≃o β) : LocallyFiniteOrderTop α
    where
  finsetIci a := (Ici (f a)).map f.symm.toEquiv.toEmbedding
  finsetIoi a := (Ioi (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp
#align order_iso.locally_finite_order_top OrderIso.locallyFiniteOrderTop
-/

#print OrderIso.locallyFiniteOrderBot /-
-- See note [reducible non-instances]
/-- Transfer `locally_finite_order_bot` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrderBot [LocallyFiniteOrderBot β] (f : α ≃o β) : LocallyFiniteOrderBot α
    where
  finsetIic a := (Iic (f a)).map f.symm.toEquiv.toEmbedding
  finsetIio a := (Iio (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp
#align order_iso.locally_finite_order_bot OrderIso.locallyFiniteOrderBot
-/

end OrderIso

/-! #### Subtype of a locally finite order -/


variable [Preorder α] (p : α → Prop) [DecidablePred p]

instance [LocallyFiniteOrder α] : LocallyFiniteOrder (Subtype p)
    where
  finsetIcc a b := (Icc (a : α) b).Subtype p
  finsetIco a b := (Ico (a : α) b).Subtype p
  finsetIoc a b := (Ioc (a : α) b).Subtype p
  finsetIoo a b := (Ioo (a : α) b).Subtype p
  finset_mem_Icc a b x := by simp_rw [Finset.mem_subtype, mem_Icc, Subtype.coe_le_coe]
  finset_mem_Ico a b x := by
    simp_rw [Finset.mem_subtype, mem_Ico, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioc a b x := by
    simp_rw [Finset.mem_subtype, mem_Ioc, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioo a b x := by simp_rw [Finset.mem_subtype, mem_Ioo, Subtype.coe_lt_coe]

instance [LocallyFiniteOrderTop α] : LocallyFiniteOrderTop (Subtype p)
    where
  finsetIci a := (Ici (a : α)).Subtype p
  finsetIoi a := (Ioi (a : α)).Subtype p
  finset_mem_Ici a x := by simp_rw [Finset.mem_subtype, mem_Ici, Subtype.coe_le_coe]
  finset_mem_Ioi a x := by simp_rw [Finset.mem_subtype, mem_Ioi, Subtype.coe_lt_coe]

instance [LocallyFiniteOrderBot α] : LocallyFiniteOrderBot (Subtype p)
    where
  finsetIic a := (Iic (a : α)).Subtype p
  finsetIio a := (Iio (a : α)).Subtype p
  finset_mem_Iic a x := by simp_rw [Finset.mem_subtype, mem_Iic, Subtype.coe_le_coe]
  finset_mem_Iio a x := by simp_rw [Finset.mem_subtype, mem_Iio, Subtype.coe_lt_coe]

namespace Finset

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : Subtype p)

#print Finset.subtype_Icc_eq /-
theorem subtype_Icc_eq : Icc a b = (Icc (a : α) b).Subtype p :=
  rfl
#align finset.subtype_Icc_eq Finset.subtype_Icc_eq
-/

#print Finset.subtype_Ico_eq /-
theorem subtype_Ico_eq : Ico a b = (Ico (a : α) b).Subtype p :=
  rfl
#align finset.subtype_Ico_eq Finset.subtype_Ico_eq
-/

#print Finset.subtype_Ioc_eq /-
theorem subtype_Ioc_eq : Ioc a b = (Ioc (a : α) b).Subtype p :=
  rfl
#align finset.subtype_Ioc_eq Finset.subtype_Ioc_eq
-/

#print Finset.subtype_Ioo_eq /-
theorem subtype_Ioo_eq : Ioo a b = (Ioo (a : α) b).Subtype p :=
  rfl
#align finset.subtype_Ioo_eq Finset.subtype_Ioo_eq
-/

variable (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x)

#print Finset.map_subtype_embedding_Icc /-
theorem map_subtype_embedding_Icc : (Icc a b).map (Embedding.subtype p) = Icc a b :=
  by
  rw [subtype_Icc_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Icc] at hx 
  exact hp hx.1 hx.2 a.prop b.prop
#align finset.map_subtype_embedding_Icc Finset.map_subtype_embedding_Icc
-/

#print Finset.map_subtype_embedding_Ico /-
theorem map_subtype_embedding_Ico : (Ico a b).map (Embedding.subtype p) = Ico a b :=
  by
  rw [subtype_Ico_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ico] at hx 
  exact hp hx.1 hx.2.le a.prop b.prop
#align finset.map_subtype_embedding_Ico Finset.map_subtype_embedding_Ico
-/

#print Finset.map_subtype_embedding_Ioc /-
theorem map_subtype_embedding_Ioc : (Ioc a b).map (Embedding.subtype p) = Ioc a b :=
  by
  rw [subtype_Ioc_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ioc] at hx 
  exact hp hx.1.le hx.2 a.prop b.prop
#align finset.map_subtype_embedding_Ioc Finset.map_subtype_embedding_Ioc
-/

#print Finset.map_subtype_embedding_Ioo /-
theorem map_subtype_embedding_Ioo : (Ioo a b).map (Embedding.subtype p) = Ioo a b :=
  by
  rw [subtype_Ioo_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ioo] at hx 
  exact hp hx.1.le hx.2.le a.prop b.prop
#align finset.map_subtype_embedding_Ioo Finset.map_subtype_embedding_Ioo
-/

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] (a : Subtype p)

#print Finset.subtype_Ici_eq /-
theorem subtype_Ici_eq : Ici a = (Ici (a : α)).Subtype p :=
  rfl
#align finset.subtype_Ici_eq Finset.subtype_Ici_eq
-/

#print Finset.subtype_Ioi_eq /-
theorem subtype_Ioi_eq : Ioi a = (Ioi (a : α)).Subtype p :=
  rfl
#align finset.subtype_Ioi_eq Finset.subtype_Ioi_eq
-/

variable (hp : ∀ ⦃a x⦄, a ≤ x → p a → p x)

#print Finset.map_subtype_embedding_Ici /-
theorem map_subtype_embedding_Ici : (Ici a).map (Embedding.subtype p) = Ici a := by
  rw [subtype_Ici_eq]; exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ici.1 hx) a.prop
#align finset.map_subtype_embedding_Ici Finset.map_subtype_embedding_Ici
-/

#print Finset.map_subtype_embedding_Ioi /-
theorem map_subtype_embedding_Ioi : (Ioi a).map (Embedding.subtype p) = Ioi a := by
  rw [subtype_Ioi_eq]; exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ioi.1 hx).le a.prop
#align finset.map_subtype_embedding_Ioi Finset.map_subtype_embedding_Ioi
-/

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] (a : Subtype p)

#print Finset.subtype_Iic_eq /-
theorem subtype_Iic_eq : Iic a = (Iic (a : α)).Subtype p :=
  rfl
#align finset.subtype_Iic_eq Finset.subtype_Iic_eq
-/

#print Finset.subtype_Iio_eq /-
theorem subtype_Iio_eq : Iio a = (Iio (a : α)).Subtype p :=
  rfl
#align finset.subtype_Iio_eq Finset.subtype_Iio_eq
-/

variable (hp : ∀ ⦃a x⦄, x ≤ a → p a → p x)

#print Finset.map_subtype_embedding_Iic /-
theorem map_subtype_embedding_Iic : (Iic a).map (Embedding.subtype p) = Iic a := by
  rw [subtype_Iic_eq]; exact Finset.subtype_map_of_mem fun x hx => hp (mem_Iic.1 hx) a.prop
#align finset.map_subtype_embedding_Iic Finset.map_subtype_embedding_Iic
-/

#print Finset.map_subtype_embedding_Iio /-
theorem map_subtype_embedding_Iio : (Iio a).map (Embedding.subtype p) = Iio a := by
  rw [subtype_Iio_eq]; exact Finset.subtype_map_of_mem fun x hx => hp (mem_Iio.1 hx).le a.prop
#align finset.map_subtype_embedding_Iio Finset.map_subtype_embedding_Iio
-/

end LocallyFiniteOrderBot

end Finset

