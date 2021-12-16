import Mathbin.Algebra.Order.Archimedean 
import Mathbin.Algebra.Order.Sub 
import Mathbin.Algebra.Order.WithZero 
import Mathbin.Order.LatticeIntervals 
import Mathbin.Order.ConditionallyCompleteLattice

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Main declarations

* `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_add_monoid` if `α` is a `linear_ordered_ring`.
* `{x : α // 0 ≤ x}` is a `linear_ordered_comm_group_with_zero` if `α` is a `linear_ordered_field`.

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
instance OrderBot [Preorderₓ α] {a : α} : OrderBot { x : α // a ≤ x } :=
  { Set.Ici.orderBot with  }

theorem bot_eq [Preorderₓ α] {a : α} : (⊥ : { x : α // a ≤ x }) = ⟨a, le_rfl⟩ :=
  rfl

instance NoTopOrder [PartialOrderₓ α] [NoTopOrder α] {a : α} : NoTopOrder { x : α // a ≤ x } :=
  Set.Ici.no_top_order

instance SemilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a ≤ x } :=
  Set.Ici.semilatticeInf

instance DenselyOrdered [Preorderₓ α] [DenselyOrdered α] {a : α} : DenselyOrdered { x : α // a ≤ x } :=
  show DenselyOrdered (Ici a) from Set.densely_ordered

/-- If `Sup ∅ ≤ a` then `{x : α // a ≤ x}` is a `conditionally_complete_linear_order`. -/
@[reducible]
protected noncomputable def ConditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α] {a : α} :
  ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  { @ordConnectedSubsetConditionallyCompleteLinearOrder α (Set.Ici a) _ ⟨⟨a, le_rfl⟩⟩ _ with  }

/-- If `Sup ∅ ≤ a` then `{x : α // a ≤ x}` is a `conditionally_complete_linear_order_bot`.

This instance uses data fields from `subtype.linear_order` to help type-class inference.
The `set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
@[reducible]
protected noncomputable def ConditionallyCompleteLinearOrderBot [ConditionallyCompleteLinearOrder α] {a : α}
  (h : Sup ∅ ≤ a) : ConditionallyCompleteLinearOrderBot { x : α // a ≤ x } :=
  { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    cSup_empty :=
      (Function.funext_iffₓ.1 (@subset_Sup_def α (Set.Ici a) _ ⟨⟨a, le_rfl⟩⟩) ∅).trans$
        Subtype.eq$
          by 
            rw [bot_eq]
            cases' h.lt_or_eq with h2 h2
            ·
              simp [h2.not_le]
            simp [h2] }

instance Inhabited [Preorderₓ α] {a : α} : Inhabited { x : α // a ≤ x } :=
  ⟨⟨a, le_rfl⟩⟩

instance HasZero [HasZero α] [Preorderₓ α] : HasZero { x : α // 0 ≤ x } :=
  ⟨⟨0, le_rfl⟩⟩

@[simp, normCast]
protected theorem coe_zero [HasZero α] [Preorderₓ α] : ((0 : { x : α // 0 ≤ x }) : α) = 0 :=
  rfl

@[simp]
theorem mk_eq_zero [HasZero α] [Preorderₓ α] {x : α} (hx : 0 ≤ x) : (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 0 ↔ x = 0 :=
  Subtype.ext_iff

instance Add [AddZeroClass α] [Preorderₓ α] [CovariantClass α α (·+·) (· ≤ ·)] : Add { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x+y, add_nonneg x.2 y.2⟩⟩

@[simp]
theorem mk_add_mk [AddZeroClass α] [Preorderₓ α] [CovariantClass α α (·+·) (· ≤ ·)] {x y : α} (hx : 0 ≤ x)
  (hy : 0 ≤ y) : ((⟨x, hx⟩ : { x : α // 0 ≤ x })+⟨y, hy⟩) = ⟨x+y, add_nonneg hx hy⟩ :=
  rfl

@[simp, normCast]
protected theorem coe_add [AddZeroClass α] [Preorderₓ α] [CovariantClass α α (·+·) (· ≤ ·)] (a b : { x : α // 0 ≤ x }) :
  ((a+b : { x : α // 0 ≤ x }) : α) = a+b :=
  rfl

instance OrderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.OrderedAddCommMonoid (coeₓ : { x : α // 0 ≤ x } → α) rfl fun x y => rfl

instance LinearOrderedAddCommMonoid [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedAddCommMonoid (coeₓ : { x : α // 0 ≤ x } → α) rfl fun x y => rfl

instance OrderedCancelAddCommMonoid [OrderedCancelAddCommMonoid α] : OrderedCancelAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.OrderedCancelAddCommMonoid (coeₓ : { x : α // 0 ≤ x } → α) rfl fun x y => rfl

instance LinearOrderedCancelAddCommMonoid [LinearOrderedCancelAddCommMonoid α] :
  LinearOrderedCancelAddCommMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedCancelAddCommMonoid (coeₓ : { x : α // 0 ≤ x } → α) rfl fun x y => rfl

/-- Coercion `{x : α // 0 ≤ x} → α` as a `add_monoid_hom`. -/
def coe_add_monoid_hom [OrderedAddCommMonoid α] : { x : α // 0 ≤ x } →+ α :=
  ⟨coeₓ, Nonneg.coe_zero, Nonneg.coe_add⟩

@[normCast]
theorem nsmul_coe [OrderedAddCommMonoid α] (n : ℕ) (r : { x : α // 0 ≤ x }) : ↑(n • r) = n • (r : α) :=
  Nonneg.coeAddMonoidHom.map_nsmul _ _

instance Archimedean [OrderedAddCommMonoid α] [Archimedean α] : Archimedean { x : α // 0 ≤ x } :=
  ⟨fun x y pos_y =>
      let ⟨n, hr⟩ := Archimedean.arch (x : α) (pos_y : (0 : α) < y)
      ⟨n,
        show (x : α) ≤ (n • y : { x : α // 0 ≤ x })by 
          simp [-nsmul_eq_mul, nsmul_coe]⟩⟩

instance HasOne [OrderedSemiring α] : HasOne { x : α // 0 ≤ x } :=
  { one := ⟨1, zero_le_one⟩ }

@[simp, normCast]
protected theorem coe_one [OrderedSemiring α] : ((1 : { x : α // 0 ≤ x }) : α) = 1 :=
  rfl

@[simp]
theorem mk_eq_one [OrderedSemiring α] {x : α} (hx : 0 ≤ x) : (⟨x, hx⟩ : { x : α // 0 ≤ x }) = 1 ↔ x = 1 :=
  Subtype.ext_iff

instance Mul [OrderedSemiring α] : Mul { x : α // 0 ≤ x } :=
  { mul := fun x y => ⟨x*y, mul_nonneg x.2 y.2⟩ }

@[simp, normCast]
protected theorem coe_mul [OrderedSemiring α] (a b : { x : α // 0 ≤ x }) : ((a*b : { x : α // 0 ≤ x }) : α) = a*b :=
  rfl

@[simp]
theorem mk_mul_mk [OrderedSemiring α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  ((⟨x, hx⟩ : { x : α // 0 ≤ x })*⟨y, hy⟩) = ⟨x*y, mul_nonneg hx hy⟩ :=
  rfl

instance OrderedSemiring [OrderedSemiring α] : OrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.OrderedSemiring (coeₓ : { x : α // 0 ≤ x } → α) rfl rfl (fun x y => rfl) fun x y => rfl

instance OrderedCommSemiring [OrderedCommSemiring α] : OrderedCommSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.OrderedCommSemiring (coeₓ : { x : α // 0 ≤ x } → α) rfl rfl (fun x y => rfl) fun x y => rfl

instance MonoidWithZeroₓ [OrderedSemiring α] : MonoidWithZeroₓ { x : α // 0 ≤ x } :=
  by 
    infer_instance

instance CommMonoidWithZero [OrderedCommSemiring α] : CommMonoidWithZero { x : α // 0 ≤ x } :=
  by 
    infer_instance

instance Nontrivial [LinearOrderedSemiring α] : Nontrivial { x : α // 0 ≤ x } :=
  ⟨⟨0, 1, fun h => zero_ne_one (congr_argₓ Subtype.val h)⟩⟩

instance LinearOrderedSemiring [LinearOrderedSemiring α] : LinearOrderedSemiring { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedSemiring (coeₓ : { x : α // 0 ≤ x } → α) rfl rfl (fun x y => rfl) fun x y => rfl

instance LinearOrderedCommMonoidWithZero [LinearOrderedCommRing α] :
  LinearOrderedCommMonoidWithZero { x : α // 0 ≤ x } :=
  { Nonneg.linearOrderedSemiring, Nonneg.orderedCommSemiring with
    mul_le_mul_left := fun a b h c => mul_le_mul_of_nonneg_left h c.2 }

/-- Coercion `{x : α // 0 ≤ x} → α` as a `ring_hom`. -/
def coe_ring_hom [OrderedSemiring α] : { x : α // 0 ≤ x } →+* α :=
  ⟨coeₓ, Nonneg.coe_one, Nonneg.coe_mul, Nonneg.coe_zero, Nonneg.coe_add⟩

instance HasInv [LinearOrderedField α] : HasInv { x : α // 0 ≤ x } :=
  { inv := fun x => ⟨x⁻¹, inv_nonneg.mpr x.2⟩ }

@[simp, normCast]
protected theorem coe_inv [LinearOrderedField α] (a : { x : α // 0 ≤ x }) : ((a⁻¹ : { x : α // 0 ≤ x }) : α) = a⁻¹ :=
  rfl

@[simp]
theorem inv_mk [LinearOrderedField α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.mpr hx⟩ :=
  rfl

instance LinearOrderedCommGroupWithZero [LinearOrderedField α] : LinearOrderedCommGroupWithZero { x : α // 0 ≤ x } :=
  { Nonneg.nontrivial, Nonneg.hasInv, Nonneg.linearOrderedCommMonoidWithZero with
    inv_zero :=
      by 
        ext 
        exact inv_zero,
    mul_inv_cancel :=
      by 
        intro a ha 
        ext 
        refine' mul_inv_cancel (mt (fun h => _) ha)
        ext 
        exact h }

instance Div [LinearOrderedField α] : Div { x : α // 0 ≤ x } :=
  { div := fun x y => ⟨x / y, div_nonneg x.2 y.2⟩ }

@[simp, normCast]
protected theorem coe_div [LinearOrderedField α] (a b : { x : α // 0 ≤ x }) :
  ((a / b : { x : α // 0 ≤ x }) : α) = a / b :=
  rfl

@[simp]
theorem mk_div_mk [LinearOrderedField α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl

instance CanonicallyOrderedAddMonoid [OrderedRing α] : CanonicallyOrderedAddMonoid { x : α // 0 ≤ x } :=
  { Nonneg.orderedAddCommMonoid, Nonneg.orderBot with
    le_iff_exists_add :=
      fun ⟨a, ha⟩ ⟨b, hb⟩ =>
        by 
          simpa only [mk_add_mk, Subtype.exists, Subtype.mk_eq_mk] using le_iff_exists_nonneg_add a b }

instance CanonicallyOrderedCommSemiring [OrderedCommRing α] [NoZeroDivisors α] :
  CanonicallyOrderedCommSemiring { x : α // 0 ≤ x } :=
  { Nonneg.canonicallyOrderedAddMonoid, Nonneg.orderedCommSemiring with
    eq_zero_or_eq_zero_of_mul_eq_zero :=
      by 
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        simp  }

instance CanonicallyLinearOrderedAddMonoid [LinearOrderedRing α] :
  CanonicallyLinearOrderedAddMonoid { x : α // 0 ≤ x } :=
  { Subtype.linearOrder _, Nonneg.canonicallyOrderedAddMonoid with  }

section LinearOrderₓ

variable [HasZero α] [LinearOrderₓ α]

/-- The function `a ↦ max a 0` of type `α → {x : α // 0 ≤ x}`. -/
def to_nonneg (a : α) : { x : α // 0 ≤ x } :=
  ⟨max a 0, le_max_rightₓ _ _⟩

@[simp]
theorem coe_to_nonneg {a : α} : (to_nonneg a : α) = max a 0 :=
  rfl

@[simp]
theorem to_nonneg_of_nonneg {a : α} (h : 0 ≤ a) : to_nonneg a = ⟨a, h⟩ :=
  by 
    simp [to_nonneg, h]

@[simp]
theorem to_nonneg_coe {a : { x : α // 0 ≤ x }} : to_nonneg (a : α) = a :=
  by 
    cases' a with a ha 
    exact to_nonneg_of_nonneg ha

@[simp]
theorem to_nonneg_le {a : α} {b : { x : α // 0 ≤ x }} : to_nonneg a ≤ b ↔ a ≤ b :=
  by 
    cases' b with b hb 
    simp [to_nonneg, hb]

@[simp]
theorem to_nonneg_lt {a : { x : α // 0 ≤ x }} {b : α} : a < to_nonneg b ↔ ↑a < b :=
  by 
    cases' a with a ha 
    simp [to_nonneg, ha.not_lt]

instance Sub [Sub α] : Sub { x : α // 0 ≤ x } :=
  ⟨fun x y => to_nonneg (x - y)⟩

@[simp]
theorem mk_sub_mk [Sub α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : { x : α // 0 ≤ x }) - ⟨y, hy⟩ = to_nonneg (x - y) :=
  rfl

end LinearOrderₓ

instance HasOrderedSub [LinearOrderedRing α] : HasOrderedSub { x : α // 0 ≤ x } :=
  ⟨by 
      rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
      simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, to_nonneg_le, Subtype.coe_mk]⟩

end Nonneg

