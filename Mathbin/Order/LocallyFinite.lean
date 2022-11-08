/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Preimage

/-!
# Locally finite orders

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

/-- A locally finite order top is an order where all intervals bounded above are finite. This is
slightly weaker than `locally_finite_order` + `order_top` as it allows empty types. -/
class LocallyFiniteOrderTop (α : Type _) [Preorder α] where
  finsetIoi : α → Finset α
  finsetIci : α → Finset α
  finset_mem_Ici : ∀ a x : α, x ∈ finset_Ici a ↔ a ≤ x
  finset_mem_Ioi : ∀ a x : α, x ∈ finset_Ioi a ↔ a < x

/-- A locally finite order bot is an order where all intervals bounded below are finite. This is
slightly weaker than `locally_finite_order` + `order_bot` as it allows empty types. -/
class LocallyFiniteOrderBot (α : Type _) [Preorder α] where
  finsetIio : α → Finset α
  finsetIic : α → Finset α
  finset_mem_Iic : ∀ a x : α, x ∈ finset_Iic a ↔ x ≤ a
  finset_mem_Iio : ∀ a x : α, x ∈ finset_Iio a ↔ x < a

/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrder.ofIcc' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Icc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) : LocallyFiniteOrder α :=
  { finsetIcc, finsetIco := fun a b => (finset_Icc a b).filter fun x => ¬b ≤ x,
    finsetIoc := fun a b => (finset_Icc a b).filter fun x => ¬x ≤ a,
    finsetIoo := fun a b => (finset_Icc a b).filter fun x => ¬x ≤ a ∧ ¬b ≤ x, finset_mem_Icc := mem_Icc,
    finset_mem_Ico := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_assoc', lt_iff_le_not_le],
    finset_mem_Ioc := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_not_le],
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_not_le, lt_iff_le_not_le] }

/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `partial_order` but only
`decidable_eq`. -/
def LocallyFiniteOrder.ofIcc (α : Type _) [PartialOrder α] [DecidableEq α] (finset_Icc : α → α → Finset α)
    (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) : LocallyFiniteOrder α :=
  { finsetIcc, finsetIco := fun a b => (finset_Icc a b).filter fun x => x ≠ b,
    finsetIoc := fun a b => (finset_Icc a b).filter fun x => a ≠ x,
    finsetIoo := fun a b => (finset_Icc a b).filter fun x => a ≠ x ∧ x ≠ b, finset_mem_Icc := mem_Icc,
    finset_mem_Ico := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_assoc', lt_iff_le_and_ne],
    finset_mem_Ioc := fun a b x => by rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_and_ne],
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_and_ne, lt_iff_le_and_ne] }

/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrderTop.ofIci' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Ici : α → Finset α) (mem_Ici : ∀ a x, x ∈ finset_Ici a ↔ a ≤ x) : LocallyFiniteOrderTop α :=
  { finsetIci, finsetIoi := fun a => (finset_Ici a).filter fun x => ¬x ≤ a, finset_mem_Ici := mem_Ici,
    finset_mem_Ioi := fun a x => by rw [mem_filter, mem_Ici, lt_iff_le_not_le] }

/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici'`, this one requires `partial_order` but
only `decidable_eq`. -/
def LocallyFiniteOrderTop.ofIci (α : Type _) [PartialOrder α] [DecidableEq α] (finset_Ici : α → Finset α)
    (mem_Ici : ∀ a x, x ∈ finset_Ici a ↔ a ≤ x) : LocallyFiniteOrderTop α :=
  { finsetIci, finsetIoi := fun a => (finset_Ici a).filter fun x => a ≠ x, finset_mem_Ici := mem_Ici,
    finset_mem_Ioi := fun a x => by rw [mem_filter, mem_Ici, lt_iff_le_and_ne] }

/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrderBot.ofIic' (α : Type _) [Preorder α] [DecidableRel ((· ≤ ·) : α → α → Prop)]
    (finset_Iic : α → Finset α) (mem_Iic : ∀ a x, x ∈ finset_Iic a ↔ x ≤ a) : LocallyFiniteOrderBot α :=
  { finsetIic, finsetIio := fun a => (finset_Iic a).filter fun x => ¬a ≤ x, finset_mem_Iic := mem_Iic,
    finset_mem_Iio := fun a x => by rw [mem_filter, mem_Iic, lt_iff_le_not_le] }

/-- A constructor from a definition of `finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order_top.of_Ici'`, this one requires `partial_order` but
only `decidable_eq`. -/
def LocallyFiniteOrderTop.ofIic (α : Type _) [PartialOrder α] [DecidableEq α] (finset_Iic : α → Finset α)
    (mem_Iic : ∀ a x, x ∈ finset_Iic a ↔ x ≤ a) : LocallyFiniteOrderBot α :=
  { finsetIic, finsetIio := fun a => (finset_Iic a).filter fun x => x ≠ a, finset_mem_Iic := mem_Iic,
    finset_mem_Iio := fun a x => by rw [mem_filter, mem_Iic, lt_iff_le_and_ne] }

variable {α β : Type _}

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[reducible]
protected def _root_.is_empty.to_locally_finite_order [Preorder α] [IsEmpty α] : LocallyFiniteOrder α where
  finsetIcc := isEmptyElim
  finsetIco := isEmptyElim
  finsetIoc := isEmptyElim
  finsetIoo := isEmptyElim
  finset_mem_Icc := isEmptyElim
  finset_mem_Ico := isEmptyElim
  finset_mem_Ioc := isEmptyElim
  finset_mem_Ioo := isEmptyElim

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[reducible]
protected def _root_.is_empty.to_locally_finite_order_top [Preorder α] [IsEmpty α] : LocallyFiniteOrderTop α where
  finsetIci := isEmptyElim
  finsetIoi := isEmptyElim
  finset_mem_Ici := isEmptyElim
  finset_mem_Ioi := isEmptyElim

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[reducible]
protected def _root_.is_empty.to_locally_finite_order_bot [Preorder α] [IsEmpty α] : LocallyFiniteOrderBot α where
  finsetIic := isEmptyElim
  finsetIio := isEmptyElim
  finset_mem_Iic := isEmptyElim
  finset_mem_Iio := isEmptyElim

/-! ### Intervals as finsets -/


namespace Finset

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b x : α}

/-- The finset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a finset.
-/
def icc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIcc a b

/-- The finset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a finset.
-/
def ico (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIco a b

/-- The finset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a finset.
-/
def ioc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoc a b

/-- The finset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a finset.
-/
def ioo (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoo a b

@[simp]
theorem mem_Icc : x ∈ icc a b ↔ a ≤ x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Icc a b x

@[simp]
theorem mem_Ico : x ∈ ico a b ↔ a ≤ x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ico a b x

@[simp]
theorem mem_Ioc : x ∈ ioc a b ↔ a < x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Ioc a b x

@[simp]
theorem mem_Ioo : x ∈ ioo a b ↔ a < x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ioo a b x

@[simp, norm_cast]
theorem coe_Icc (a b : α) : (icc a b : Set α) = Set.IccCat a b :=
  Set.ext fun _ => mem_Icc

@[simp, norm_cast]
theorem coe_Ico (a b : α) : (ico a b : Set α) = Set.IcoCat a b :=
  Set.ext fun _ => mem_Ico

@[simp, norm_cast]
theorem coe_Ioc (a b : α) : (ioc a b : Set α) = Set.IocCat a b :=
  Set.ext fun _ => mem_Ioc

@[simp, norm_cast]
theorem coe_Ioo (a b : α) : (ioo a b : Set α) = Set.IooCat a b :=
  Set.ext fun _ => mem_Ioo

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a x : α}

/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a finset. -/
def ici (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIci a

/-- The finset of elements `x` such that `a < x`. Basically `set.Ioi a` as a finset. -/
def ioi (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIoi a

@[simp]
theorem mem_Ici : x ∈ ici a ↔ a ≤ x :=
  LocallyFiniteOrderTop.finset_mem_Ici _ _

@[simp]
theorem mem_Ioi : x ∈ ioi a ↔ a < x :=
  LocallyFiniteOrderTop.finset_mem_Ioi _ _

@[simp, norm_cast]
theorem coe_Ici (a : α) : (ici a : Set α) = Set.IciCat a :=
  Set.ext fun _ => mem_Ici

@[simp, norm_cast]
theorem coe_Ioi (a : α) : (ioi a : Set α) = Set.IoiCat a :=
  Set.ext fun _ => mem_Ioi

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a x : α}

/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Iic a` as a finset. -/
def iic (a : α) : Finset α :=
  LocallyFiniteOrderBot.finsetIic a

/-- The finset of elements `x` such that `a < x`. Basically `set.Iio a` as a finset. -/
def iio (a : α) : Finset α :=
  LocallyFiniteOrderBot.finsetIio a

@[simp]
theorem mem_Iic : x ∈ iic a ↔ x ≤ a :=
  LocallyFiniteOrderBot.finset_mem_Iic _ _

@[simp]
theorem mem_Iio : x ∈ iio a ↔ x < a :=
  LocallyFiniteOrderBot.finset_mem_Iio _ _

@[simp, norm_cast]
theorem coe_Iic (a : α) : (iic a : Set α) = Set.IicCat a :=
  Set.ext fun _ => mem_Iic

@[simp, norm_cast]
theorem coe_Iio (a : α) : (iio a : Set α) = Set.IioCat a :=
  Set.ext fun _ => mem_Iio

end LocallyFiniteOrderBot

section OrderTop

variable [LocallyFiniteOrder α] [OrderTop α] {a x : α}

-- See note [lower priority instance]
instance (priority := 100) _root_.locally_finite_order.to_locally_finite_order_top : LocallyFiniteOrderTop α where
  finsetIci b := icc b ⊤
  finsetIoi b := ioc b ⊤
  finset_mem_Ici a x := by rw [mem_Icc, and_iff_left le_top]
  finset_mem_Ioi a x := by rw [mem_Ioc, and_iff_left le_top]

theorem Ici_eq_Icc (a : α) : ici a = icc a ⊤ :=
  rfl

theorem Ioi_eq_Ioc (a : α) : ioi a = ioc a ⊤ :=
  rfl

end OrderTop

section OrderBot

variable [OrderBot α] [LocallyFiniteOrder α] {b x : α}

-- See note [lower priority instance]
instance (priority := 100) LocallyFiniteOrder.toLocallyFiniteOrderBot : LocallyFiniteOrderBot α where
  finsetIic := icc ⊥
  finsetIio := ico ⊥
  finset_mem_Iic a x := by rw [mem_Icc, and_iff_right bot_le]
  finset_mem_Iio a x := by rw [mem_Ico, and_iff_right bot_le]

theorem Iic_eq_Icc : Iic = icc (⊥ : α) :=
  rfl

theorem Iio_eq_Ico : Iio = ico (⊥ : α) :=
  rfl

end OrderBot

end Finset

/-! ### Intervals as multisets -/


namespace Multiset

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

/-- The multiset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a
multiset. -/
def icc (a b : α) : Multiset α :=
  (Finset.icc a b).val

/-- The multiset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a
multiset. -/
def ico (a b : α) : Multiset α :=
  (Finset.ico a b).val

/-- The multiset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a
multiset. -/
def ioc (a b : α) : Multiset α :=
  (Finset.ioc a b).val

/-- The multiset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a
multiset. -/
def ioo (a b : α) : Multiset α :=
  (Finset.ioo a b).val

@[simp]
theorem mem_Icc {a b x : α} : x ∈ icc a b ↔ a ≤ x ∧ x ≤ b := by rw [Icc, ← Finset.mem_def, Finset.mem_Icc]

@[simp]
theorem mem_Ico {a b x : α} : x ∈ ico a b ↔ a ≤ x ∧ x < b := by rw [Ico, ← Finset.mem_def, Finset.mem_Ico]

@[simp]
theorem mem_Ioc {a b x : α} : x ∈ ioc a b ↔ a < x ∧ x ≤ b := by rw [Ioc, ← Finset.mem_def, Finset.mem_Ioc]

@[simp]
theorem mem_Ioo {a b x : α} : x ∈ ioo a b ↔ a < x ∧ x < b := by rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

/-- The multiset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a multiset. -/
def ici (a : α) : Multiset α :=
  (Finset.ici a).val

/-- The multiset of elements `x` such that `a < x`. Basically `set.Ioi a` as a multiset. -/
def ioi (a : α) : Multiset α :=
  (Finset.ioi a).val

@[simp]
theorem mem_Ici {a x : α} : x ∈ ici a ↔ a ≤ x := by rw [Ici, ← Finset.mem_def, Finset.mem_Ici]

@[simp]
theorem mem_Ioi {a x : α} : x ∈ ioi a ↔ a < x := by rw [Ioi, ← Finset.mem_def, Finset.mem_Ioi]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

/-- The multiset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a multiset. -/
def iic (b : α) : Multiset α :=
  (Finset.iic b).val

/-- The multiset of elements `x` such that `x < b`. Basically `set.Iio b` as a multiset. -/
def iio (b : α) : Multiset α :=
  (Finset.iio b).val

@[simp]
theorem mem_Iic {b x : α} : x ∈ iic b ↔ x ≤ b := by rw [Iic, ← Finset.mem_def, Finset.mem_Iic]

@[simp]
theorem mem_Iio {b x : α} : x ∈ iio b ↔ x < b := by rw [Iio, ← Finset.mem_def, Finset.mem_Iio]

end LocallyFiniteOrderBot

end Multiset

/-! ### Finiteness of `set` intervals -/


namespace Set

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] (a b : α)

instance fintypeIcc : Fintype (IccCat a b) :=
  Fintype.ofFinset (Finset.icc a b) fun x => by rw [Finset.mem_Icc, mem_Icc]

instance fintypeIco : Fintype (IcoCat a b) :=
  Fintype.ofFinset (Finset.ico a b) fun x => by rw [Finset.mem_Ico, mem_Ico]

instance fintypeIoc : Fintype (IocCat a b) :=
  Fintype.ofFinset (Finset.ioc a b) fun x => by rw [Finset.mem_Ioc, mem_Ioc]

instance fintypeIoo : Fintype (IooCat a b) :=
  Fintype.ofFinset (Finset.ioo a b) fun x => by rw [Finset.mem_Ioo, mem_Ioo]

theorem finite_Icc : (IccCat a b).Finite :=
  (IccCat a b).to_finite

theorem finite_Ico : (IcoCat a b).Finite :=
  (IcoCat a b).to_finite

theorem finite_Ioc : (IocCat a b).Finite :=
  (IocCat a b).to_finite

theorem finite_Ioo : (IooCat a b).Finite :=
  (IooCat a b).to_finite

end Preorder

section OrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] (a : α)

instance fintypeIci : Fintype (IciCat a) :=
  Fintype.ofFinset (Finset.ici a) fun x => by rw [Finset.mem_Ici, mem_Ici]

instance fintypeIoi : Fintype (IoiCat a) :=
  Fintype.ofFinset (Finset.ioi a) fun x => by rw [Finset.mem_Ioi, mem_Ioi]

theorem finite_Ici : (IciCat a).Finite :=
  (IciCat a).to_finite

theorem finite_Ioi : (IoiCat a).Finite :=
  (IoiCat a).to_finite

end OrderTop

section OrderBot

variable [Preorder α] [LocallyFiniteOrderBot α] (b : α)

instance fintypeIic : Fintype (IicCat b) :=
  Fintype.ofFinset (Finset.iic b) fun x => by rw [Finset.mem_Iic, mem_Iic]

instance fintypeIio : Fintype (IioCat b) :=
  Fintype.ofFinset (Finset.iio b) fun x => by rw [Finset.mem_Iio, mem_Iio]

theorem finite_Iic : (IicCat b).Finite :=
  (IicCat b).to_finite

theorem finite_Iio : (IioCat b).Finite :=
  (IioCat b).to_finite

end OrderBot

end Set

/-! ### Instances -/


open Finset

section Preorder

variable [Preorder α] [Preorder β]

/-- A noncomputable constructor from the finiteness of all closed intervals. -/
noncomputable def LocallyFiniteOrder.ofFiniteIcc (h : ∀ a b : α, (Set.IccCat a b).Finite) : LocallyFiniteOrder α :=
  @LocallyFiniteOrder.ofIcc' α _ (Classical.decRel _) (fun a b => (h a b).toFinset) fun a b x => by
    rw [Set.Finite.mem_to_finset, Set.mem_Icc]

/-- A fintype is a locally finite order.

This is not an instance as it would not be defeq to better instances such as
`fin.locally_finite_order`.
-/
@[reducible]
def Fintype.toLocallyFiniteOrder [Fintype α] [@DecidableRel α (· < ·)] [@DecidableRel α (· ≤ ·)] :
    LocallyFiniteOrder α where
  finsetIcc a b := (Set.IccCat a b).toFinset
  finsetIco a b := (Set.IcoCat a b).toFinset
  finsetIoc a b := (Set.IocCat a b).toFinset
  finsetIoo a b := (Set.IooCat a b).toFinset
  finset_mem_Icc a b x := by simp only [Set.mem_to_finset, Set.mem_Icc]
  finset_mem_Ico a b x := by simp only [Set.mem_to_finset, Set.mem_Ico]
  finset_mem_Ioc a b x := by simp only [Set.mem_to_finset, Set.mem_Ioc]
  finset_mem_Ioo a b x := by simp only [Set.mem_to_finset, Set.mem_Ioo]

instance : Subsingleton (LocallyFiniteOrder α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIcc : h₀_finset_Icc = h₁_finset_Icc := by
      ext (a b x)
      rw [h₀_finset_mem_Icc, h₁_finset_mem_Icc]
    have hIco : h₀_finset_Ico = h₁_finset_Ico := by
      ext (a b x)
      rw [h₀_finset_mem_Ico, h₁_finset_mem_Ico]
    have hIoc : h₀_finset_Ioc = h₁_finset_Ioc := by
      ext (a b x)
      rw [h₀_finset_mem_Ioc, h₁_finset_mem_Ioc]
    have hIoo : h₀_finset_Ioo = h₁_finset_Ioo := by
      ext (a b x)
      rw [h₀_finset_mem_Ioo, h₁_finset_mem_Ioo]
    simp_rw [hIcc, hIco, hIoc, hIoo]

instance : Subsingleton (LocallyFiniteOrderTop α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIci : h₀_finset_Ici = h₁_finset_Ici := by
      ext (a b x)
      rw [h₀_finset_mem_Ici, h₁_finset_mem_Ici]
    have hIoi : h₀_finset_Ioi = h₁_finset_Ioi := by
      ext (a b x)
      rw [h₀_finset_mem_Ioi, h₁_finset_mem_Ioi]
    simp_rw [hIci, hIoi]

instance : Subsingleton (LocallyFiniteOrderBot α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIic : h₀_finset_Iic = h₁_finset_Iic := by
      ext (a b x)
      rw [h₀_finset_mem_Iic, h₁_finset_mem_Iic]
    have hIio : h₀_finset_Iio = h₁_finset_Iio := by
      ext (a b x)
      rw [h₀_finset_mem_Iio, h₁_finset_mem_Iio]
    simp_rw [hIic, hIio]

-- Should this be called `locally_finite_order.lift`?
/-- Given an order embedding `α ↪o β`, pulls back the `locally_finite_order` on `β` to `α`. -/
protected noncomputable def OrderEmbedding.locallyFiniteOrder [LocallyFiniteOrder β] (f : α ↪o β) :
    LocallyFiniteOrder α where
  finsetIcc a b := (icc (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIco a b := (ico (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIoc a b := (ioc (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finsetIoo a b := (ioo (f a) (f b)).Preimage f (f.toEmbedding.Injective.InjOn _)
  finset_mem_Icc a b x := by rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le]
  finset_mem_Ico a b x := by rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt]
  finset_mem_Ioc a b x := by rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le]
  finset_mem_Ioo a b x := by rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt]

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
instance : LocallyFiniteOrder αᵒᵈ where
  finsetIcc a b := @icc α _ _ (ofDual b) (ofDual a)
  finsetIco a b := @ioc α _ _ (ofDual b) (ofDual a)
  finsetIoc a b := @ico α _ _ (ofDual b) (ofDual a)
  finsetIoo a b := @ioo α _ _ (ofDual b) (ofDual a)
  finset_mem_Icc a b x := mem_Icc.trans (and_comm' _ _)
  finset_mem_Ico a b x := mem_Ioc.trans (and_comm' _ _)
  finset_mem_Ioc a b x := mem_Ico.trans (and_comm' _ _)
  finset_mem_Ioo a b x := mem_Ioo.trans (and_comm' _ _)

theorem Icc_to_dual : icc (toDual a) (toDual b) = (icc b a).map toDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Icc, mem_Icc]
  exact and_comm' _ _

theorem Ico_to_dual : ico (toDual a) (toDual b) = (ioc b a).map toDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ico, mem_Ioc]
  exact and_comm' _ _

theorem Ioc_to_dual : ioc (toDual a) (toDual b) = (ico b a).map toDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioc, mem_Ico]
  exact and_comm' _ _

theorem Ioo_to_dual : ioo (toDual a) (toDual b) = (ioo b a).map toDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioo, mem_Ioo]
  exact and_comm' _ _

theorem Icc_of_dual (a b : αᵒᵈ) : icc (ofDual a) (ofDual b) = (icc b a).map ofDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Icc, mem_Icc]
  exact and_comm' _ _

theorem Ico_of_dual (a b : αᵒᵈ) : ico (ofDual a) (ofDual b) = (ioc b a).map ofDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ico, mem_Ioc]
  exact and_comm' _ _

theorem Ioc_of_dual (a b : αᵒᵈ) : ioc (ofDual a) (ofDual b) = (ico b a).map ofDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioc, mem_Ico]
  exact and_comm' _ _

theorem Ioo_of_dual (a b : αᵒᵈ) : ioo (ofDual a) (ofDual b) = (ioo b a).map ofDual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioo, mem_Ioo]
  exact and_comm' _ _

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

/-- Note we define `Iic (to_dual a)` as `Ici a` (which has type `finset α` not `finset αᵒᵈ`!)
instead of `(Ici a).map to_dual.to_embedding` as this means the following is defeq:
```
lemma this : (Iic (to_dual (to_dual a)) : _) = (Iic a : _) := rfl
```
-/
instance : LocallyFiniteOrderBot αᵒᵈ where
  finsetIic a := @ici α _ _ (ofDual a)
  finsetIio a := @ioi α _ _ (ofDual a)
  finset_mem_Iic a x := mem_Ici
  finset_mem_Iio a x := mem_Ioi

theorem Iic_to_dual (a : α) : iic (toDual a) = (ici a).map toDual.toEmbedding :=
  map_refl.symm

theorem Iio_to_dual (a : α) : iio (toDual a) = (ioi a).map toDual.toEmbedding :=
  map_refl.symm

theorem Ici_of_dual (a : αᵒᵈ) : ici (ofDual a) = (iic a).map ofDual.toEmbedding :=
  map_refl.symm

theorem Ioi_of_dual (a : αᵒᵈ) : ioi (ofDual a) = (iio a).map ofDual.toEmbedding :=
  map_refl.symm

end LocallyFiniteOrderTop

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderBot α]

/-- Note we define `Ici (to_dual a)` as `Iic a` (which has type `finset α` not `finset αᵒᵈ`!)
instead of `(Iic a).map to_dual.to_embedding` as this means the following is defeq:
```
lemma this : (Ici (to_dual (to_dual a)) : _) = (Ici a : _) := rfl
```
-/
instance : LocallyFiniteOrderTop αᵒᵈ where
  finsetIci a := @iic α _ _ (ofDual a)
  finsetIoi a := @iio α _ _ (ofDual a)
  finset_mem_Ici a x := mem_Iic
  finset_mem_Ioi a x := mem_Iio

theorem Ici_to_dual (a : α) : ici (toDual a) = (iic a).map toDual.toEmbedding :=
  map_refl.symm

theorem Ioi_to_dual (a : α) : ioi (toDual a) = (iio a).map toDual.toEmbedding :=
  map_refl.symm

theorem Iic_of_dual (a : αᵒᵈ) : iic (ofDual a) = (ici a).map ofDual.toEmbedding :=
  map_refl.symm

theorem Iio_of_dual (a : αᵒᵈ) : iio (ofDual a) = (ioi a).map ofDual.toEmbedding :=
  map_refl.symm

end LocallyFiniteOrderTop

namespace Prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] :
    LocallyFiniteOrder (α × β) :=
  LocallyFiniteOrder.ofIcc' (α × β) (fun a b => icc a.fst b.fst ×ˢ icc a.snd b.snd) fun a b x => by
    rw [mem_product, mem_Icc, mem_Icc, and_and_and_comm]
    rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β] [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] :
    LocallyFiniteOrderTop (α × β) :=
  LocallyFiniteOrderTop.ofIci' (α × β) (fun a => ici a.fst ×ˢ ici a.snd) fun a x => by
    rw [mem_product, mem_Ici, mem_Ici]
    rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β] [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)] :
    LocallyFiniteOrderBot (α × β) :=
  LocallyFiniteOrderBot.ofIic' (α × β) (fun a => iic a.fst ×ˢ iic a.snd) fun a x => by
    rw [mem_product, mem_Iic, mem_Iic]
    rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Icc_eq [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)]
    (p q : α × β) : Finset.icc p q = Finset.icc p.1 q.1 ×ˢ Finset.icc p.2 q.2 :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Icc_mk_mk [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)]
    (a₁ a₂ : α) (b₁ b₂ : β) : Finset.icc (a₁, b₁) (a₂, b₂) = Finset.icc a₁ a₂ ×ˢ Finset.icc b₁ b₂ :=
  rfl

theorem card_Icc [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableRel ((· ≤ ·) : α × β → α × β → Prop)]
    (p q : α × β) : (Finset.icc p q).card = (Finset.icc p.1 q.1).card * (Finset.icc p.2 q.2).card :=
  Finset.card_product _ _

end Prod

end Preorder

/-!
#### `with_top`, `with_bot`

Adding a `⊤` to a locally finite `order_top` keeps it locally finite.
Adding a `⊥` to a locally finite `order_bot` keeps it locally finite.
-/


namespace WithTop

variable (α) [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α]

attribute [local match_pattern] coe

attribute [local simp] Option.mem_iff

instance : LocallyFiniteOrder (WithTop α) where
  finsetIcc a b :=
    match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insertNone (ici a)
    | (a : α), (b : α) => (icc a b).map Embedding.coeOption
  finsetIco a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (ici a).map Embedding.coeOption
    | (a : α), (b : α) => (ico a b).map Embedding.coeOption
  finsetIoc a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => insertNone (ioi a)
    | (a : α), (b : α) => (ioc a b).map Embedding.coeOption
  finsetIoo a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (ioi a).map Embedding.coeOption
    | (a : α), (b : α) => (ioo a b).map Embedding.coeOption
  finset_mem_Icc a b x :=
    match a, b, x with
    | ⊤, ⊤, x => mem_singleton.trans (le_antisymm_iff.trans <| and_comm' _ _)
    | ⊤, (b : α), x => iff_of_false (not_mem_empty _) fun h => (h.1.trans h.2).not_lt <| coe_lt_top _
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
    | (a : α), (b : α), (x : α) => by simp [WithTop.LocallyFiniteOrder._match2, coe_eq_coe, coe_lt_coe]
  finset_mem_Ioc a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans_le h.2
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match3, coe_lt_top]
    | (a : α), ⊤, (x : α) => by simp [WithTop.LocallyFiniteOrder._match3, coe_eq_coe, coe_lt_coe]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match3]
    | (a : α), (b : α), (x : α) => by simp [WithTop.LocallyFiniteOrder._match3, coe_eq_coe, coe_lt_coe]
  finset_mem_Ioo a b x :=
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt <| h.1.trans h.2
    | (a : α), ⊤, ⊤ => by simp [WithTop.LocallyFiniteOrder._match4, coe_lt_top]
    | (a : α), ⊤, (x : α) => by simp [WithTop.LocallyFiniteOrder._match4, coe_eq_coe, coe_lt_coe, coe_lt_top]
    | (a : α), (b : α), ⊤ => by simp [WithTop.LocallyFiniteOrder._match4]
    | (a : α), (b : α), (x : α) => by simp [WithTop.LocallyFiniteOrder._match4, coe_eq_coe, coe_lt_coe]

variable (a b : α)

theorem Icc_coe_top : icc (a : WithTop α) ⊤ = insertNone (ici a) :=
  rfl

theorem Icc_coe_coe : icc (a : WithTop α) b = (icc a b).map Embedding.coeOption :=
  rfl

theorem Ico_coe_top : ico (a : WithTop α) ⊤ = (ici a).map Embedding.coeOption :=
  rfl

theorem Ico_coe_coe : ico (a : WithTop α) b = (ico a b).map Embedding.coeOption :=
  rfl

theorem Ioc_coe_top : ioc (a : WithTop α) ⊤ = insertNone (ioi a) :=
  rfl

theorem Ioc_coe_coe : ioc (a : WithTop α) b = (ioc a b).map Embedding.coeOption :=
  rfl

theorem Ioo_coe_top : ioo (a : WithTop α) ⊤ = (ioi a).map Embedding.coeOption :=
  rfl

theorem Ioo_coe_coe : ioo (a : WithTop α) b = (ioo a b).map Embedding.coeOption :=
  rfl

end WithTop

namespace WithBot

variable (α) [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α]

instance : LocallyFiniteOrder (WithBot α) :=
  @OrderDual.locallyFiniteOrder (WithTop αᵒᵈ) _ _

variable (a b : α)

theorem Icc_bot_coe : icc (⊥ : WithBot α) b = insertNone (iic b) :=
  rfl

theorem Icc_coe_coe : icc (a : WithBot α) b = (icc a b).map Embedding.coeOption :=
  rfl

theorem Ico_bot_coe : ico (⊥ : WithBot α) b = insertNone (iio b) :=
  rfl

theorem Ico_coe_coe : ico (a : WithBot α) b = (ico a b).map Embedding.coeOption :=
  rfl

theorem Ioc_bot_coe : ioc (⊥ : WithBot α) b = (iic b).map Embedding.coeOption :=
  rfl

theorem Ioc_coe_coe : ioc (a : WithBot α) b = (ioc a b).map Embedding.coeOption :=
  rfl

theorem Ioo_bot_coe : ioo (⊥ : WithBot α) b = (iio b).map Embedding.coeOption :=
  rfl

theorem Ioo_coe_coe : ioo (a : WithBot α) b = (ioo a b).map Embedding.coeOption :=
  rfl

end WithBot

namespace OrderIso

variable [Preorder α] [Preorder β]

/-! #### Transfer locally finite orders across order isomorphisms -/


-- See note [reducible non-instances]
/-- Transfer `locally_finite_order` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrder [LocallyFiniteOrder β] (f : α ≃o β) : LocallyFiniteOrder α where
  finsetIcc a b := (icc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIco a b := (ico (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoc a b := (ioc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoo a b := (ioo (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp

-- See note [reducible non-instances]
/-- Transfer `locally_finite_order_top` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrderTop [LocallyFiniteOrderTop β] (f : α ≃o β) : LocallyFiniteOrderTop α where
  finsetIci a := (ici (f a)).map f.symm.toEquiv.toEmbedding
  finsetIoi a := (ioi (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

-- See note [reducible non-instances]
/-- Transfer `locally_finite_order_bot` across an `order_iso`. -/
@[reducible]
def locallyFiniteOrderBot [LocallyFiniteOrderBot β] (f : α ≃o β) : LocallyFiniteOrderBot α where
  finsetIic a := (iic (f a)).map f.symm.toEquiv.toEmbedding
  finsetIio a := (iio (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

end OrderIso

/-! #### Subtype of a locally finite order -/


variable [Preorder α] (p : α → Prop) [DecidablePred p]

instance [LocallyFiniteOrder α] : LocallyFiniteOrder (Subtype p) where
  finsetIcc a b := (icc (a : α) b).Subtype p
  finsetIco a b := (ico (a : α) b).Subtype p
  finsetIoc a b := (ioc (a : α) b).Subtype p
  finsetIoo a b := (ioo (a : α) b).Subtype p
  finset_mem_Icc a b x := by simp_rw [Finset.mem_subtype, mem_Icc, Subtype.coe_le_coe]
  finset_mem_Ico a b x := by simp_rw [Finset.mem_subtype, mem_Ico, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioc a b x := by simp_rw [Finset.mem_subtype, mem_Ioc, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioo a b x := by simp_rw [Finset.mem_subtype, mem_Ioo, Subtype.coe_lt_coe]

instance [LocallyFiniteOrderTop α] : LocallyFiniteOrderTop (Subtype p) where
  finsetIci a := (ici (a : α)).Subtype p
  finsetIoi a := (ioi (a : α)).Subtype p
  finset_mem_Ici a x := by simp_rw [Finset.mem_subtype, mem_Ici, Subtype.coe_le_coe]
  finset_mem_Ioi a x := by simp_rw [Finset.mem_subtype, mem_Ioi, Subtype.coe_lt_coe]

instance [LocallyFiniteOrderBot α] : LocallyFiniteOrderBot (Subtype p) where
  finsetIic a := (iic (a : α)).Subtype p
  finsetIio a := (iio (a : α)).Subtype p
  finset_mem_Iic a x := by simp_rw [Finset.mem_subtype, mem_Iic, Subtype.coe_le_coe]
  finset_mem_Iio a x := by simp_rw [Finset.mem_subtype, mem_Iio, Subtype.coe_lt_coe]

namespace Finset

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : Subtype p)

theorem subtype_Icc_eq : icc a b = (icc (a : α) b).Subtype p :=
  rfl

theorem subtype_Ico_eq : ico a b = (ico (a : α) b).Subtype p :=
  rfl

theorem subtype_Ioc_eq : ioc a b = (ioc (a : α) b).Subtype p :=
  rfl

theorem subtype_Ioo_eq : ioo a b = (ioo (a : α) b).Subtype p :=
  rfl

variable (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x)

include hp

theorem map_subtype_embedding_Icc : (icc a b).map (Embedding.subtype p) = icc a b := by
  rw [subtype_Icc_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Icc] at hx
  exact hp hx.1 hx.2 a.prop b.prop

theorem map_subtype_embedding_Ico : (ico a b).map (Embedding.subtype p) = ico a b := by
  rw [subtype_Ico_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ico] at hx
  exact hp hx.1 hx.2.le a.prop b.prop

theorem map_subtype_embedding_Ioc : (ioc a b).map (Embedding.subtype p) = ioc a b := by
  rw [subtype_Ioc_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ioc] at hx
  exact hp hx.1.le hx.2 a.prop b.prop

theorem map_subtype_embedding_Ioo : (ioo a b).map (Embedding.subtype p) = ioo a b := by
  rw [subtype_Ioo_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ioo] at hx
  exact hp hx.1.le hx.2.le a.prop b.prop

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] (a : Subtype p)

theorem subtype_Ici_eq : ici a = (ici (a : α)).Subtype p :=
  rfl

theorem subtype_Ioi_eq : ioi a = (ioi (a : α)).Subtype p :=
  rfl

variable (hp : ∀ ⦃a x⦄, a ≤ x → p a → p x)

include hp

theorem map_subtype_embedding_Ici : (ici a).map (Embedding.subtype p) = ici a := by
  rw [subtype_Ici_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ici.1 hx) a.prop

theorem map_subtype_embedding_Ioi : (ioi a).map (Embedding.subtype p) = ioi a := by
  rw [subtype_Ioi_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ioi.1 hx).le a.prop

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] (a : Subtype p)

theorem subtype_Iic_eq : iic a = (iic (a : α)).Subtype p :=
  rfl

theorem subtype_Iio_eq : iio a = (iio (a : α)).Subtype p :=
  rfl

variable (hp : ∀ ⦃a x⦄, x ≤ a → p a → p x)

include hp

theorem map_subtype_embedding_Iic : (iic a).map (Embedding.subtype p) = iic a := by
  rw [subtype_Iic_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Iic.1 hx) a.prop

theorem map_subtype_embedding_Iio : (iio a).map (Embedding.subtype p) = iio a := by
  rw [subtype_Iio_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Iio.1 hx).le a.prop

end LocallyFiniteOrderBot

end Finset

