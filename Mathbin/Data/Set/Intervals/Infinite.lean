/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathbin.Data.Set.Finite

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/


variable {α : Type _} [Preorder α]

/-- A nonempty preorder with no maximal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
theorem NoMaxOrder.infinite [Nonempty α] [NoMaxOrder α] : Infinite α :=
  let ⟨f, hf⟩ := Nat.exists_strict_mono α
  Infinite.of_injective f hf.Injective
#align no_max_order.infinite NoMaxOrder.infinite

/-- A nonempty preorder with no minimal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
theorem NoMinOrder.infinite [Nonempty α] [NoMinOrder α] : Infinite α :=
  @NoMaxOrder.infinite αᵒᵈ _ _ _
#align no_min_order.infinite NoMinOrder.infinite

namespace Set

section DenselyOrdered

variable [DenselyOrdered α] {a b : α} (h : a < b)

theorem IooCat.infinite : Infinite (IooCat a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _
#align set.Ioo.infinite Set.IooCat.infinite

theorem Ioo_infinite : (IooCat a b).Infinite :=
  infinite_coe_iff.1 <| IooCat.infinite h
#align set.Ioo_infinite Set.Ioo_infinite

theorem Ico_infinite : (IcoCat a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ico_self
#align set.Ico_infinite Set.Ico_infinite

theorem IcoCat.infinite : Infinite (IcoCat a b) :=
  infinite_coe_iff.2 <| Ico_infinite h
#align set.Ico.infinite Set.IcoCat.infinite

theorem Ioc_infinite : (IocCat a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ioc_self
#align set.Ioc_infinite Set.Ioc_infinite

theorem IocCat.infinite : Infinite (IocCat a b) :=
  infinite_coe_iff.2 <| Ioc_infinite h
#align set.Ioc.infinite Set.IocCat.infinite

theorem Icc_infinite : (IccCat a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self
#align set.Icc_infinite Set.Icc_infinite

theorem IccCat.infinite : Infinite (IccCat a b) :=
  infinite_coe_iff.2 <| Icc_infinite h
#align set.Icc.infinite Set.IccCat.infinite

end DenselyOrdered

instance [NoMinOrder α] {a : α} : Infinite (IioCat a) :=
  NoMinOrder.infinite

theorem Iio_infinite [NoMinOrder α] (a : α) : (IioCat a).Infinite :=
  infinite_coe_iff.1 IioCat.infinite
#align set.Iio_infinite Set.Iio_infinite

instance [NoMinOrder α] {a : α} : Infinite (IicCat a) :=
  NoMinOrder.infinite

theorem Iic_infinite [NoMinOrder α] (a : α) : (IicCat a).Infinite :=
  infinite_coe_iff.1 IicCat.infinite
#align set.Iic_infinite Set.Iic_infinite

instance [NoMaxOrder α] {a : α} : Infinite (IoiCat a) :=
  NoMaxOrder.infinite

theorem Ioi_infinite [NoMinOrder α] (a : α) : (IioCat a).Infinite :=
  infinite_coe_iff.1 IioCat.infinite
#align set.Ioi_infinite Set.Ioi_infinite

instance [NoMaxOrder α] {a : α} : Infinite (IciCat a) :=
  NoMaxOrder.infinite

theorem Ici_infinite [NoMaxOrder α] (a : α) : (IciCat a).Infinite :=
  infinite_coe_iff.1 IciCat.infinite
#align set.Ici_infinite Set.Ici_infinite

end Set

