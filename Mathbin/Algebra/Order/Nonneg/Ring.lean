/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Algebra.Order.Ring.Defs
import Mathbin.Algebra.Order.Ring.InjSurj
import Mathbin.Order.CompleteLatticeIntervals
import Mathbin.Order.LatticeIntervals

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Main declarations

* `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_add_monoid` if `α` is a `linear_ordered_ring`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing and element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `set.Ici` to this subtype.
-/


open Set

variable {α : Type _}

namespace Nonneg

/-- This instance uses data fields from `subtype.partial_order` to help type-class inference.
The `set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
instance orderBot [Preorder α] {a : α} : OrderBot { x : α // a ≤ x } :=
  { Set.IciCat.orderBot with }

theorem bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a ≤ x }) = ⟨a, le_rfl⟩ :=
  rfl

instance no_max_order [PartialOrder α] [NoMaxOrder α] {a : α} : NoMaxOrder { x : α // a ≤ x } :=
  Set.IciCat.no_max_order

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup { x : α // a ≤ x } :=
  Set.IciCat.semilatticeSup

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a ≤ x } :=
  Set.IciCat.semilatticeInf

instance distribLattice [DistribLattice α] {a : α} : DistribLattice { x : α // a ≤ x } :=
  Set.IciCat.distribLattice

instance densely_ordered [Preorder α] [DenselyOrdered α] {a : α} : DenselyOrdered { x : α // a ≤ x } :=
  show DenselyOrdered (IciCat a) from Set.densely_ordered

/-- If `Sup ∅ ≤ a` then `{x : α // a ≤ x}` is a `conditionally_complete_linear_order`. -/
@[reducible]
protected noncomputable def conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α] {a : α} :
    ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  { @ordConnectedSubsetConditionallyCompleteLinearOrder α (Set.IciCat a) _ ⟨⟨a, le_rfl⟩⟩ _ with }

/-- If `Sup ∅ ≤ a` then `{x : α // a ≤ x}` is a `conditionally_complete_linear_order_bot`.

This instance uses data fields from `subtype.linear_order` to help type-class inference.
The `set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
@[reducible]
protected noncomputable def conditionallyCompleteLinearOrderBot [ConditionallyCompleteLinearOrder α] {a : α}
    (h : sup ∅ ≤ a) : ConditionallyCompleteLinearOrderBot { x : α // a ≤ x } :=
  { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    cSup_empty :=
      (Function.funext_iff.1 (@subset_Sup_def α (Set.IciCat a) _ ⟨⟨a, le_rfl⟩⟩) ∅).trans <|
        Subtype.eq <| by
          rw [bot_eq]
          cases' h.lt_or_eq with h2 h2
          · simp [h2.not_le]
            
          simp [h2] }

instance inhabited [Preorder α] {a : α} : Inhabited { x : α // a ≤ x } :=
  ⟨⟨a, le_rfl⟩⟩

instance hasZero [Zero α] [Preorder α] : Zero { x : α // 0 ≤ x } :=
  ⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]
protected theorem coe_zero [Zero α] [Preorder α] : ((0 : { x : α // 0 ≤ x }) : α) = 0 :=
  rfl

@[simp]
theorem mk_eq_zero [Zero α] [Preorder α] {x : α} (hx : 0 ≤ x) : (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 0 ↔ x = 0 :=
  Subtype.ext_iff

instance hasAdd [AddZeroClass α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] : Add { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp]
theorem mk_add_mk [AddZeroClass α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] {x y : α} (hx : 0 ≤ x)
    (hy : 0 ≤ y) : (⟨x, hx⟩ : { x : α // 0 ≤ x }) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
  rfl

@[simp, norm_cast]
protected theorem coe_add [AddZeroClass α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (a b : { x : α // 0 ≤ x }) : ((a + b : { x : α // 0 ≤ x }) : α) = a + b :=
  rfl

instance hasNsmul [AddMonoid α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] : HasSmul ℕ { x : α // 0 ≤ x } :=
  ⟨fun n x => ⟨n • x, nsmul_nonneg x.Prop n⟩⟩

@[simp]
theorem nsmul_mk [AddMonoid α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] (n : ℕ) {x : α} (hx : 0 ≤ x) :
    (n • ⟨x, hx⟩ : { x : α // 0 ≤ x }) = ⟨n • x, nsmul_nonneg hx n⟩ :=
  rfl

@[simp, norm_cast]
protected theorem coe_nsmul [AddMonoid α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)] (n : ℕ)
    (a : { x : α // 0 ≤ x }) : ((n • a : { x : α // 0 ≤ x }) : α) = n • a :=
  rfl

instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.OrderedAddCommMonoid _ rfl (fun x y => rfl) fun _ _ => rfl

instance linearOrderedAddCommMonoid [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedAddCommMonoid _ rfl (fun x y => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ =>
    rfl

instance orderedCancelAddCommMonoid [OrderedCancelAddCommMonoid α] : OrderedCancelAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.OrderedCancelAddCommMonoid _ rfl (fun x y => rfl) fun _ _ => rfl

instance linearOrderedCancelAddCommMonoid [LinearOrderedCancelAddCommMonoid α] :
    LinearOrderedCancelAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedCancelAddCommMonoid _ rfl (fun x y => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

/-- Coercion `{x : α // 0 ≤ x} → α` as a `add_monoid_hom`. -/
def coeAddMonoidHom [OrderedAddCommMonoid α] : { x : α // 0 ≤ x } →+ α :=
  ⟨coe, Nonneg.coe_zero, Nonneg.coe_add⟩

@[norm_cast]
theorem nsmul_coe [OrderedAddCommMonoid α] (n : ℕ) (r : { x : α // 0 ≤ x }) : ↑(n • r) = n • (r : α) :=
  Nonneg.coeAddMonoidHom.map_nsmul _ _

instance hasOne [OrderedSemiring α] : One { x : α // 0 ≤ x } where one := ⟨1, zero_le_one⟩

@[simp, norm_cast]
protected theorem coe_one [OrderedSemiring α] : ((1 : { x : α // 0 ≤ x }) : α) = 1 :=
  rfl

@[simp]
theorem mk_eq_one [OrderedSemiring α] {x : α} (hx : 0 ≤ x) : (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 1 ↔ x = 1 :=
  Subtype.ext_iff

instance hasMul [OrderedSemiring α] : Mul { x : α // 0 ≤ x } where mul x y := ⟨x * y, mul_nonneg x.2 y.2⟩

@[simp, norm_cast]
protected theorem coe_mul [OrderedSemiring α] (a b : { x : α // 0 ≤ x }) : ((a * b : { x : α // 0 ≤ x }) : α) = a * b :=
  rfl

@[simp]
theorem mk_mul_mk [OrderedSemiring α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
  rfl

instance addMonoidWithOne [OrderedSemiring α] : AddMonoidWithOne { x : α // 0 ≤ x } :=
  { Nonneg.hasOne, Nonneg.orderedAddCommMonoid with natCast := fun n => ⟨n, Nat.cast_nonneg n⟩,
    nat_cast_zero := by simp [Nat.cast], nat_cast_succ := fun _ => by simp [Nat.cast] <;> rfl }

@[simp, norm_cast]
protected theorem coe_nat_cast [OrderedSemiring α] (n : ℕ) : ((↑n : { x : α // 0 ≤ x }) : α) = n :=
  rfl

@[simp]
theorem mk_nat_cast [OrderedSemiring α] (n : ℕ) : (⟨n, n.cast_nonneg⟩ : { x : α // 0 ≤ x }) = n :=
  rfl

instance hasPow [OrderedSemiring α] : Pow { x : α // 0 ≤ x } ℕ where pow x n := ⟨x ^ n, pow_nonneg x.2 n⟩

@[simp, norm_cast]
protected theorem coe_pow [OrderedSemiring α] (a : { x : α // 0 ≤ x }) (n : ℕ) : (↑(a ^ n) : α) = a ^ n :=
  rfl

@[simp]
theorem mk_pow [OrderedSemiring α] {x : α} (hx : 0 ≤ x) (n : ℕ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ :=
  rfl

instance orderedSemiring [OrderedSemiring α] : OrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.OrderedSemiring _ rfl rfl (fun x y => rfl) (fun x y => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ => rfl

instance strictOrderedSemiring [StrictOrderedSemiring α] : StrictOrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.StrictOrderedSemiring _ rfl rfl (fun x y => rfl) (fun x y => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance orderedCommSemiring [OrderedCommSemiring α] : OrderedCommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.OrderedCommSemiring _ rfl rfl (fun x y => rfl) (fun x y => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance strictOrderedCommSemiring [StrictOrderedCommSemiring α] : StrictOrderedCommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.StrictOrderedCommSemiring _ rfl rfl (fun x y => rfl) (fun x y => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

-- These prevent noncomputable instances being found, as it does not require `linear_order` which
-- is frequently non-computable.
instance monoidWithZero [OrderedSemiring α] : MonoidWithZero { x : α // 0 ≤ x } := by infer_instance

instance commMonoidWithZero [OrderedCommSemiring α] : CommMonoidWithZero { x : α // 0 ≤ x } := by infer_instance

instance semiring [OrderedSemiring α] : Semiring { x : α // 0 ≤ x } :=
  inferInstance

instance commSemiring [OrderedCommSemiring α] : CommSemiring { x : α // 0 ≤ x } :=
  inferInstance

instance nontrivial [LinearOrderedSemiring α] : Nontrivial { x : α // 0 ≤ x } :=
  ⟨⟨0, 1, fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩

instance linearOrderedSemiring [LinearOrderedSemiring α] : LinearOrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedSemiring _ rfl rfl (fun x y => rfl) (fun x y => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance linearOrderedCommMonoidWithZero [LinearOrderedCommRing α] :
    LinearOrderedCommMonoidWithZero { x : α // 0 ≤ x } :=
  { Nonneg.linearOrderedSemiring, Nonneg.orderedCommSemiring with
    mul_le_mul_left := fun a b h c => mul_le_mul_of_nonneg_left h c.2 }

/-- Coercion `{x : α // 0 ≤ x} → α` as a `ring_hom`. -/
def coeRingHom [OrderedSemiring α] : { x : α // 0 ≤ x } →+* α :=
  ⟨coe, Nonneg.coe_one, Nonneg.coe_mul, Nonneg.coe_zero, Nonneg.coe_add⟩

instance canonicallyOrderedAddMonoid [OrderedRing α] : CanonicallyOrderedAddMonoid { x : α // 0 ≤ x } :=
  { Nonneg.orderedAddCommMonoid, Nonneg.orderBot with le_self_add := fun a b => le_add_of_nonneg_right b.2,
    exists_add_of_le := fun a b h => ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel'_right _ _).symm⟩ }

instance canonicallyOrderedCommSemiring [OrderedCommRing α] [NoZeroDivisors α] :
    CanonicallyOrderedCommSemiring { x : α // 0 ≤ x } :=
  { Nonneg.canonicallyOrderedAddMonoid, Nonneg.orderedCommSemiring with
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp }

instance canonicallyLinearOrderedAddMonoid [LinearOrderedRing α] :
    CanonicallyLinearOrderedAddMonoid { x : α // 0 ≤ x } :=
  { Subtype.linearOrder _, Nonneg.canonicallyOrderedAddMonoid with }

section LinearOrder

variable [Zero α] [LinearOrder α]

/-- The function `a ↦ max a 0` of type `α → {x : α // 0 ≤ x}`. -/
def toNonneg (a : α) : { x : α // 0 ≤ x } :=
  ⟨max a 0, le_max_right _ _⟩

@[simp]
theorem coe_to_nonneg {a : α} : (toNonneg a : α) = max a 0 :=
  rfl

@[simp]
theorem to_nonneg_of_nonneg {a : α} (h : 0 ≤ a) : toNonneg a = ⟨a, h⟩ := by simp [to_nonneg, h]

@[simp]
theorem to_nonneg_coe {a : { x : α // 0 ≤ x }} : toNonneg (a : α) = a := by
  cases' a with a ha
  exact to_nonneg_of_nonneg ha

@[simp]
theorem to_nonneg_le {a : α} {b : { x : α // 0 ≤ x }} : toNonneg a ≤ b ↔ a ≤ b := by
  cases' b with b hb
  simp [to_nonneg, hb]

@[simp]
theorem to_nonneg_lt {a : { x : α // 0 ≤ x }} {b : α} : a < toNonneg b ↔ ↑a < b := by
  cases' a with a ha
  simp [to_nonneg, ha.not_lt]

instance hasSub [Sub α] : Sub { x : α // 0 ≤ x } :=
  ⟨fun x y => toNonneg (x - y)⟩

@[simp]
theorem mk_sub_mk [Sub α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) - ⟨y, hy⟩ = toNonneg (x - y) :=
  rfl

end LinearOrder

instance hasOrderedSub [LinearOrderedRing α] : HasOrderedSub { x : α // 0 ≤ x } :=
  ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, to_nonneg_le, Subtype.coe_mk]⟩

end Nonneg

