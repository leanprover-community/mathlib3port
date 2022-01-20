import Mathbin.Data.Finset.Preimage

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

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

When it's also an `order_top`,
* `finset.Ici`: Closed-infinite interval as a finset.
* `finset.Ioi`: Open-infinite interval as a finset.
* `multiset.Ici`: Closed-infinite interval as a multiset.
* `multiset.Ioi`: Open-infinite interval as a multiset.

When it's also an `order_bot`,
* `finset.Iic`: Infinite-open interval as a finset.
* `finset.Iio`: Infinite-closed interval as a finset.
* `multiset.Iic`: Infinite-open interval as a multiset.
* `multiset.Iio`: Infinite-closed interval as a multiset.

## Instances

A `locally_finite_order` instance can be built
* for a subtype of a locally finite order. See `subtype.locally_finite_order`.
* for the product of two locally finite orders. See `prod.locally_finite_order`.
* for any fintype (but it is noncomputable). See `fintype.to_locally_finite_order`.
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
class LocallyFiniteOrder (α : Type _) [Preorderₓ α] where
  finsetIcc : α → α → Finset α
  finsetIco : α → α → Finset α
  finsetIoc : α → α → Finset α
  finsetIoo : α → α → Finset α
  finset_mem_Icc : ∀ a b x : α, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b
  finset_mem_Ico : ∀ a b x : α, x ∈ finset_Ico a b ↔ a ≤ x ∧ x < b
  finset_mem_Ioc : ∀ a b x : α, x ∈ finset_Ioc a b ↔ a < x ∧ x ≤ b
  finset_mem_Ioo : ∀ a b x : α, x ∈ finset_Ioo a b ↔ a < x ∧ x < b

/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def LocallyFiniteOrder.ofIcc' (α : Type _) [Preorderₓ α] [DecidableRel (· ≤ · : α → α → Prop)]
    (finset_Icc : α → α → Finset α) (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) : LocallyFiniteOrder α :=
  { finsetIcc, finsetIco := fun a b => (finset_Icc a b).filter fun x => ¬b ≤ x,
    finsetIoc := fun a b => (finset_Icc a b).filter fun x => ¬x ≤ a,
    finsetIoo := fun a b => (finset_Icc a b).filter fun x => ¬x ≤ a ∧ ¬b ≤ x, finset_mem_Icc := mem_Icc,
    finset_mem_Ico := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_not_leₓ],
    finset_mem_Ioc := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, And.right_comm, lt_iff_le_not_leₓ],
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_not_leₓ, lt_iff_le_not_leₓ] }

/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `partial_order` but only
`decidable_eq`. -/
def LocallyFiniteOrder.ofIcc (α : Type _) [PartialOrderₓ α] [DecidableEq α] (finset_Icc : α → α → Finset α)
    (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) : LocallyFiniteOrder α :=
  { finsetIcc, finsetIco := fun a b => (finset_Icc a b).filter fun x => x ≠ b,
    finsetIoc := fun a b => (finset_Icc a b).filter fun x => a ≠ x,
    finsetIoo := fun a b => (finset_Icc a b).filter fun x => a ≠ x ∧ x ≠ b, finset_mem_Icc := mem_Icc,
    finset_mem_Ico := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_and_ne],
    finset_mem_Ioc := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, And.right_comm, lt_iff_le_and_ne],
    finset_mem_Ioo := fun a b x => by
      rw [Finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_and_ne, lt_iff_le_and_ne] }

variable {α β : Type _}

/-! ### Intervals as finsets -/


namespace Finset

section Preorderₓ

variable [Preorderₓ α] [LocallyFiniteOrder α]

/-- The finset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a finset.
-/
def Icc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIcc a b

/-- The finset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a finset.
-/
def Ico (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIco a b

/-- The finset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a finset.
-/
def Ioc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoc a b

/-- The finset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a finset.
-/
def Ioo (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoo a b

@[simp]
theorem mem_Icc {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Icc a b x

@[simp]
theorem mem_Ico {a b x : α} : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ico a b x

@[simp]
theorem mem_Ioc {a b x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Ioc a b x

@[simp]
theorem mem_Ioo {a b x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ioo a b x

@[simp, norm_cast]
theorem coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b := by
  ext
  rw [mem_coe, mem_Icc, Set.mem_Icc]

@[simp, norm_cast]
theorem coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b := by
  ext
  rw [mem_coe, mem_Ico, Set.mem_Ico]

@[simp, norm_cast]
theorem coe_Ioc (a b : α) : (Ioc a b : Set α) = Set.Ioc a b := by
  ext
  rw [mem_coe, mem_Ioc, Set.mem_Ioc]

@[simp, norm_cast]
theorem coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b := by
  ext
  rw [mem_coe, mem_Ioo, Set.mem_Ioo]

theorem Ico_subset_Ico {a₁ b₁ a₂ b₂ : α} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := by
  rintro x hx
  rw [mem_Ico] at hx⊢
  exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩

end Preorderₓ

section OrderTop

variable [Preorderₓ α] [OrderTop α] [LocallyFiniteOrder α]

/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a finset. -/
def Ici (a : α) : Finset α :=
  Icc a ⊤

/-- The finset of elements `x` such that `a < x`. Basically `set.Ioi a` as a finset. -/
def Ioi (a : α) : Finset α :=
  Ioc a ⊤

theorem Ici_eq_Icc (a : α) : Ici a = Icc a ⊤ :=
  rfl

theorem Ioi_eq_Ioc (a : α) : Ioi a = Ioc a ⊤ :=
  rfl

@[simp, norm_cast]
theorem coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a := by
  rw [Ici, coe_Icc, Set.Icc_top]

@[simp, norm_cast]
theorem coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a := by
  rw [Ioi, coe_Ioc, Set.Ioc_top]

@[simp]
theorem mem_Ici {a x : α} : x ∈ Ici a ↔ a ≤ x := by
  rw [← Set.mem_Ici, ← coe_Ici, mem_coe]

@[simp]
theorem mem_Ioi {a x : α} : x ∈ Ioi a ↔ a < x := by
  rw [← Set.mem_Ioi, ← coe_Ioi, mem_coe]

end OrderTop

section OrderBot

variable [Preorderₓ α] [OrderBot α] [LocallyFiniteOrder α]

/-- The finset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a finset. -/
def Iic (b : α) : Finset α :=
  Icc ⊥ b

/-- The finset of elements `x` such that `x < b`. Basically `set.Iio b` as a finset. -/
def Iio (b : α) : Finset α :=
  Ico ⊥ b

theorem Iic_eq_Icc : Iic = Icc (⊥ : α) :=
  rfl

theorem Iio_eq_Ico : Iio = Ico (⊥ : α) :=
  rfl

@[simp, norm_cast]
theorem coe_Iic (b : α) : (Iic b : Set α) = Set.Iic b := by
  rw [Iic, coe_Icc, Set.Icc_bot]

@[simp, norm_cast]
theorem coe_Iio (b : α) : (Iio b : Set α) = Set.Iio b := by
  rw [Iio, coe_Ico, Set.Ico_bot]

@[simp]
theorem mem_Iic {b x : α} : x ∈ Iic b ↔ x ≤ b := by
  rw [← Set.mem_Iic, ← coe_Iic, mem_coe]

@[simp]
theorem mem_Iio {b x : α} : x ∈ Iio b ↔ x < b := by
  rw [← Set.mem_Iio, ← coe_Iio, mem_coe]

end OrderBot

end Finset

/-! ### Intervals as multisets -/


namespace Multiset

section Preorderₓ

variable [Preorderₓ α] [LocallyFiniteOrder α]

/-- The multiset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a
multiset. -/
def Icc (a b : α) : Multiset α :=
  (Finset.icc a b).val

/-- The multiset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a
multiset. -/
def Ico (a b : α) : Multiset α :=
  (Finset.ico a b).val

/-- The multiset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a
multiset. -/
def Ioc (a b : α) : Multiset α :=
  (Finset.ioc a b).val

/-- The multiset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a
multiset. -/
def Ioo (a b : α) : Multiset α :=
  (Finset.ioo a b).val

@[simp]
theorem mem_Icc {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := by
  rw [Icc, ← Finset.mem_def, Finset.mem_Icc]

@[simp]
theorem mem_Ico {a b x : α} : x ∈ Ico a b ↔ a ≤ x ∧ x < b := by
  rw [Ico, ← Finset.mem_def, Finset.mem_Ico]

@[simp]
theorem mem_Ioc {a b x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := by
  rw [Ioc, ← Finset.mem_def, Finset.mem_Ioc]

@[simp]
theorem mem_Ioo {a b x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b := by
  rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]

end Preorderₓ

section OrderTop

variable [Preorderₓ α] [OrderTop α] [LocallyFiniteOrder α]

/-- The multiset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a multiset. -/
def Ici (a : α) : Multiset α :=
  (Finset.ici a).val

/-- The multiset of elements `x` such that `a < x`. Basically `set.Ioi a` as a multiset. -/
def Ioi (a : α) : Multiset α :=
  (Finset.ioi a).val

@[simp]
theorem mem_Ici {a x : α} : x ∈ Ici a ↔ a ≤ x := by
  rw [Ici, ← Finset.mem_def, Finset.mem_Ici]

@[simp]
theorem mem_Ioi {a x : α} : x ∈ Ioi a ↔ a < x := by
  rw [Ioi, ← Finset.mem_def, Finset.mem_Ioi]

end OrderTop

section OrderBot

variable [Preorderₓ α] [OrderBot α] [LocallyFiniteOrder α]

/-- The multiset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a multiset. -/
def Iic (b : α) : Multiset α :=
  (Finset.iic b).val

/-- The multiset of elements `x` such that `x < b`. Basically `set.Iio b` as a multiset. -/
def Iio (b : α) : Multiset α :=
  (Finset.iio b).val

@[simp]
theorem mem_Iic {b x : α} : x ∈ Iic b ↔ x ≤ b := by
  rw [Iic, ← Finset.mem_def, Finset.mem_Iic]

@[simp]
theorem mem_Iio {b x : α} : x ∈ Iio b ↔ x < b := by
  rw [Iio, ← Finset.mem_def, Finset.mem_Iio]

end OrderBot

end Multiset

/-! ### Finiteness of `set` intervals -/


namespace Set

section Preorderₓ

variable [Preorderₓ α] [LocallyFiniteOrder α] (a b : α)

instance fintype_Icc : Fintype (Icc a b) :=
  Fintype.ofFinset (Finset.icc a b) fun x => by
    rw [Finset.mem_Icc, mem_Icc]

instance fintype_Ico : Fintype (Ico a b) :=
  Fintype.ofFinset (Finset.ico a b) fun x => by
    rw [Finset.mem_Ico, mem_Ico]

instance fintype_Ioc : Fintype (Ioc a b) :=
  Fintype.ofFinset (Finset.ioc a b) fun x => by
    rw [Finset.mem_Ioc, mem_Ioc]

instance fintype_Ioo : Fintype (Ioo a b) :=
  Fintype.ofFinset (Finset.ioo a b) fun x => by
    rw [Finset.mem_Ioo, mem_Ioo]

theorem finite_Icc : (Icc a b).Finite :=
  ⟨Set.fintypeIcc a b⟩

theorem finite_Ico : (Ico a b).Finite :=
  ⟨Set.fintypeIco a b⟩

theorem finite_Ioc : (Ioc a b).Finite :=
  ⟨Set.fintypeIoc a b⟩

theorem finite_Ioo : (Ioo a b).Finite :=
  ⟨Set.fintypeIoo a b⟩

end Preorderₓ

section OrderTop

variable [Preorderₓ α] [OrderTop α] [LocallyFiniteOrder α] (a : α)

instance fintype_Ici : Fintype (Ici a) :=
  Fintype.ofFinset (Finset.ici a) fun x => by
    rw [Finset.mem_Ici, mem_Ici]

instance fintype_Ioi : Fintype (Ioi a) :=
  Fintype.ofFinset (Finset.ioi a) fun x => by
    rw [Finset.mem_Ioi, mem_Ioi]

theorem finite_Ici : (Ici a).Finite :=
  ⟨Set.fintypeIci a⟩

theorem finite_Ioi : (Ioi a).Finite :=
  ⟨Set.fintypeIoi a⟩

end OrderTop

section OrderBot

variable [Preorderₓ α] [OrderBot α] [LocallyFiniteOrder α] (b : α)

instance fintype_Iic : Fintype (Iic b) :=
  Fintype.ofFinset (Finset.iic b) fun x => by
    rw [Finset.mem_Iic, mem_Iic]

instance fintype_Iio : Fintype (Iio b) :=
  Fintype.ofFinset (Finset.iio b) fun x => by
    rw [Finset.mem_Iio, mem_Iio]

theorem finite_Iic : (Iic b).Finite :=
  ⟨Set.fintypeIic b⟩

theorem finite_Iio : (Iio b).Finite :=
  ⟨Set.fintypeIio b⟩

end OrderBot

end Set

/-! ### Instances -/


open Finset

section Preorderₓ

variable [Preorderₓ α]

/-- A noncomputable constructor from the finiteness of all closed intervals. -/
noncomputable def LocallyFiniteOrder.ofFiniteIcc (h : ∀ a b : α, (Set.Icc a b).Finite) : LocallyFiniteOrder α :=
  @LocallyFiniteOrder.ofIcc' α _ (Classical.decRel _) (fun a b => (h a b).toFinset) fun a b x => by
    rw [Set.Finite.mem_to_finset, Set.mem_Icc]

/-- A fintype is noncomputably a locally finite order. -/
noncomputable def Fintype.toLocallyFiniteOrder [Fintype α] : LocallyFiniteOrder α where
  finsetIcc := fun a b => (Set.Finite.of_fintype (Set.Icc a b)).toFinset
  finsetIco := fun a b => (Set.Finite.of_fintype (Set.Ico a b)).toFinset
  finsetIoc := fun a b => (Set.Finite.of_fintype (Set.Ioc a b)).toFinset
  finsetIoo := fun a b => (Set.Finite.of_fintype (Set.Ioo a b)).toFinset
  finset_mem_Icc := fun a b x => by
    rw [Set.Finite.mem_to_finset, Set.mem_Icc]
  finset_mem_Ico := fun a b x => by
    rw [Set.Finite.mem_to_finset, Set.mem_Ico]
  finset_mem_Ioc := fun a b x => by
    rw [Set.Finite.mem_to_finset, Set.mem_Ioc]
  finset_mem_Ioo := fun a b x => by
    rw [Set.Finite.mem_to_finset, Set.mem_Ioo]

instance : Subsingleton (LocallyFiniteOrder α) :=
  Subsingleton.intro fun h₀ h₁ => by
    cases h₀
    cases h₁
    have hIcc : h₀_finset_Icc = h₁_finset_Icc := by
      ext a b x
      rw [h₀_finset_mem_Icc, h₁_finset_mem_Icc]
    have hIco : h₀_finset_Ico = h₁_finset_Ico := by
      ext a b x
      rw [h₀_finset_mem_Ico, h₁_finset_mem_Ico]
    have hIoc : h₀_finset_Ioc = h₁_finset_Ioc := by
      ext a b x
      rw [h₀_finset_mem_Ioc, h₁_finset_mem_Ioc]
    have hIoo : h₀_finset_Ioo = h₁_finset_Ioo := by
      ext a b x
      rw [h₀_finset_mem_Ioo, h₁_finset_mem_Ioo]
    simp_rw [hIcc, hIco, hIoc, hIoo]

variable [Preorderₓ β] [LocallyFiniteOrder β]

/-- Given an order embedding `α ↪o β`, pulls back the `locally_finite_order` on `β` to `α`. -/
noncomputable def OrderEmbedding.locallyFiniteOrder (f : α ↪o β) : LocallyFiniteOrder α where
  finsetIcc := fun a b => (Icc (f a) (f b)).Preimage f (f.to_embedding.injective.inj_on _)
  finsetIco := fun a b => (Ico (f a) (f b)).Preimage f (f.to_embedding.injective.inj_on _)
  finsetIoc := fun a b => (Ioc (f a) (f b)).Preimage f (f.to_embedding.injective.inj_on _)
  finsetIoo := fun a b => (Ioo (f a) (f b)).Preimage f (f.to_embedding.injective.inj_on _)
  finset_mem_Icc := fun a b x => by
    rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le]
  finset_mem_Ico := fun a b x => by
    rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt]
  finset_mem_Ioc := fun a b x => by
    rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le]
  finset_mem_Ioo := fun a b x => by
    rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt]

open OrderDual

variable [LocallyFiniteOrder α] (a b : α)

/-- Note we define `Icc (to_dual a) (to_dual b)` as `Icc α _ _ b a` (which has type `finset α` not
`finset (order_dual α)`!) instead of `(Icc b a).map to_dual.to_embedding` as this means the
following is defeq:
```
lemma this : (Icc (to_dual (to_dual a)) (to_dual (to_dual b)) : _) = (Icc a b : _) := rfl
```
-/
instance : LocallyFiniteOrder (OrderDual α) where
  finsetIcc := fun a b => @Icc α _ _ (of_dual b) (of_dual a)
  finsetIco := fun a b => @Ioc α _ _ (of_dual b) (of_dual a)
  finsetIoc := fun a b => @Ico α _ _ (of_dual b) (of_dual a)
  finsetIoo := fun a b => @Ioo α _ _ (of_dual b) (of_dual a)
  finset_mem_Icc := fun a b x => mem_Icc.trans (and_comm _ _)
  finset_mem_Ico := fun a b x => mem_Ioc.trans (and_comm _ _)
  finset_mem_Ioc := fun a b x => mem_Ico.trans (and_comm _ _)
  finset_mem_Ioo := fun a b x => mem_Ioo.trans (and_comm _ _)

theorem Icc_to_dual : Icc (to_dual a) (to_dual b) = (Icc b a).map to_dual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Icc, mem_Icc]
  exact and_comm _ _

theorem Ico_to_dual : Ico (to_dual a) (to_dual b) = (Ioc b a).map to_dual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ico, mem_Ioc]
  exact and_comm _ _

theorem Ioc_to_dual : Ioc (to_dual a) (to_dual b) = (Ico b a).map to_dual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioc, mem_Ico]
  exact and_comm _ _

theorem Ioo_to_dual : Ioo (to_dual a) (to_dual b) = (Ioo b a).map to_dual.toEmbedding := by
  refine' Eq.trans _ map_refl.symm
  ext c
  rw [mem_Ioo, mem_Ioo]
  exact and_comm _ _

instance [DecidableRel (· ≤ · : α × β → α × β → Prop)] : LocallyFiniteOrder (α × β) :=
  LocallyFiniteOrder.ofIcc' (α × β) (fun a b => (Icc a.fst b.fst).product (Icc a.snd b.snd)) fun a b x => by
    rw [mem_product, mem_Icc, mem_Icc, and_and_and_comm]
    rfl

end Preorderₓ

/-!
#### `with_top`, `with_bot`

Adding a `⊤` to a locally finite `order_top` keeps it locally finite.
Adding a `⊥` to a locally finite `order_bot` keeps it locally finite.
-/


namespace WithTop

variable (α) [PartialOrderₓ α] [OrderTop α] [LocallyFiniteOrder α]

attribute [local matchPattern] coeₓ

attribute [local simp] Option.mem_iff

instance : LocallyFiniteOrder (WithTop α) where
  finsetIcc := fun a b =>
    match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insert_none (Ici a)
    | (a : α), (b : α) => (Icc a b).map embedding.coe_option
  finsetIco := fun a b =>
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ici a).map embedding.coe_option
    | (a : α), (b : α) => (Ico a b).map embedding.coe_option
  finsetIoc := fun a b =>
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => insert_none (Ioi a)
    | (a : α), (b : α) => (Ioc a b).map embedding.coe_option
  finsetIoo := fun a b =>
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ioi a).map embedding.coe_option
    | (a : α), (b : α) => (Ioo a b).map embedding.coe_option
  finset_mem_Icc := fun a b x =>
    match a, b, x with
    | ⊤, ⊤, x => mem_singleton.trans (le_antisymm_iffₓ.trans $ and_comm _ _)
    | ⊤, (b : α), x => iff_of_false (not_mem_empty _) fun h => (h.1.trans h.2).not_lt $ coe_lt_top _
    | (a : α), ⊤, ⊤ => by
      simp [WithTop.LocallyFiniteOrder._match1]
    | (a : α), ⊤, (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match1, coe_eq_coe]
    | (a : α), (b : α), ⊤ => by
      simp [WithTop.LocallyFiniteOrder._match1]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match1, coe_eq_coe]
  finset_mem_Ico := fun a b x =>
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt $ h.1.trans_lt h.2
    | (a : α), ⊤, ⊤ => by
      simp [WithTop.LocallyFiniteOrder._match2]
    | (a : α), ⊤, (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match2, coe_eq_coe, coe_lt_top]
    | (a : α), (b : α), ⊤ => by
      simp [WithTop.LocallyFiniteOrder._match2]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match2, coe_eq_coe, coe_lt_coe]
  finset_mem_Ioc := fun a b x =>
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt $ h.1.trans_le h.2
    | (a : α), ⊤, ⊤ => by
      simp [WithTop.LocallyFiniteOrder._match3, coe_lt_top]
    | (a : α), ⊤, (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match3, coe_eq_coe, coe_lt_coe]
    | (a : α), (b : α), ⊤ => by
      simp [WithTop.LocallyFiniteOrder._match3]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match3, coe_eq_coe, coe_lt_coe]
  finset_mem_Ioo := fun a b x =>
    match a, b, x with
    | ⊤, b, x => iff_of_false (not_mem_empty _) fun h => not_top_lt $ h.1.trans h.2
    | (a : α), ⊤, ⊤ => by
      simp [WithTop.LocallyFiniteOrder._match4, coe_lt_top]
    | (a : α), ⊤, (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match4, coe_eq_coe, coe_lt_coe, coe_lt_top]
    | (a : α), (b : α), ⊤ => by
      simp [WithTop.LocallyFiniteOrder._match4]
    | (a : α), (b : α), (x : α) => by
      simp [WithTop.LocallyFiniteOrder._match4, coe_eq_coe, coe_lt_coe]

variable (a b : α)

theorem Icc_coe_top : Icc (a : WithTop α) ⊤ = insert_none (Ici a) :=
  rfl

theorem Icc_coe_coe : Icc (a : WithTop α) b = (Icc a b).map embedding.coe_option :=
  rfl

theorem Ico_coe_top : Ico (a : WithTop α) ⊤ = (Ici a).map embedding.coe_option :=
  rfl

theorem Ico_coe_coe : Ico (a : WithTop α) b = (Ico a b).map embedding.coe_option :=
  rfl

theorem Ioc_coe_top : Ioc (a : WithTop α) ⊤ = insert_none (Ioi a) :=
  rfl

theorem Ioc_coe_coe : Ioc (a : WithTop α) b = (Ioc a b).map embedding.coe_option :=
  rfl

theorem Ioo_coe_top : Ioo (a : WithTop α) ⊤ = (Ioi a).map embedding.coe_option :=
  rfl

theorem Ioo_coe_coe : Ioo (a : WithTop α) b = (Ioo a b).map embedding.coe_option :=
  rfl

end WithTop

namespace WithBot

variable (α) [PartialOrderₓ α] [OrderBot α] [LocallyFiniteOrder α]

instance : LocallyFiniteOrder (WithBot α) :=
  @OrderDual.locallyFiniteOrder (WithTop (OrderDual α)) _ _

variable (a b : α)

theorem Icc_bot_coe : Icc (⊥ : WithBot α) b = insert_none (Iic b) :=
  rfl

theorem Icc_coe_coe : Icc (a : WithBot α) b = (Icc a b).map embedding.coe_option :=
  rfl

theorem Ico_bot_coe : Ico (⊥ : WithBot α) b = insert_none (Iio b) :=
  rfl

theorem Ico_coe_coe : Ico (a : WithBot α) b = (Ico a b).map embedding.coe_option :=
  rfl

theorem Ioc_bot_coe : Ioc (⊥ : WithBot α) b = (Iic b).map embedding.coe_option :=
  rfl

theorem Ioc_coe_coe : Ioc (a : WithBot α) b = (Ioc a b).map embedding.coe_option :=
  rfl

theorem Ioo_bot_coe : Ioo (⊥ : WithBot α) b = (Iio b).map embedding.coe_option :=
  rfl

theorem Ioo_coe_coe : Ioo (a : WithBot α) b = (Ioo a b).map embedding.coe_option :=
  rfl

end WithBot

/-! #### Subtype of a locally finite order -/


variable [Preorderₓ α] [LocallyFiniteOrder α] (p : α → Prop) [DecidablePred p]

instance : LocallyFiniteOrder (Subtype p) where
  finsetIcc := fun a b => (Icc (a : α) b).Subtype p
  finsetIco := fun a b => (Ico (a : α) b).Subtype p
  finsetIoc := fun a b => (Ioc (a : α) b).Subtype p
  finsetIoo := fun a b => (Ioo (a : α) b).Subtype p
  finset_mem_Icc := fun a b x => by
    simp_rw [Finset.mem_subtype, mem_Icc, Subtype.coe_le_coe]
  finset_mem_Ico := fun a b x => by
    simp_rw [Finset.mem_subtype, mem_Ico, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioc := fun a b x => by
    simp_rw [Finset.mem_subtype, mem_Ioc, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioo := fun a b x => by
    simp_rw [Finset.mem_subtype, mem_Ioo, Subtype.coe_lt_coe]

variable (a b : Subtype p)

namespace Finset

theorem subtype_Icc_eq : Icc a b = (Icc (a : α) b).Subtype p :=
  rfl

theorem subtype_Ico_eq : Ico a b = (Ico (a : α) b).Subtype p :=
  rfl

theorem subtype_Ioc_eq : Ioc a b = (Ioc (a : α) b).Subtype p :=
  rfl

theorem subtype_Ioo_eq : Ioo a b = (Ioo (a : α) b).Subtype p :=
  rfl

variable (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x)

include hp

theorem map_subtype_embedding_Icc : (Icc a b).map (Function.Embedding.subtype p) = Icc (a : α) b := by
  rw [subtype_Icc_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Icc] at hx
  exact hp hx.1 hx.2 a.prop b.prop

theorem map_subtype_embedding_Ico : (Ico a b).map (Function.Embedding.subtype p) = Ico (a : α) b := by
  rw [subtype_Ico_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ico] at hx
  exact hp hx.1 hx.2.le a.prop b.prop

theorem map_subtype_embedding_Ioc : (Ioc a b).map (Function.Embedding.subtype p) = Ioc (a : α) b := by
  rw [subtype_Ioc_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ioc] at hx
  exact hp hx.1.le hx.2 a.prop b.prop

theorem map_subtype_embedding_Ioo : (Ioo a b).map (Function.Embedding.subtype p) = Ioo (a : α) b := by
  rw [subtype_Ioo_eq]
  refine' Finset.subtype_map_of_mem fun x hx => _
  rw [mem_Ioo] at hx
  exact hp hx.1.le hx.2.le a.prop b.prop

end Finset

