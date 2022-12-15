/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

! This file was ported from Lean 3 source module data.set.intervals.infinite
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
  let ⟨f, hf⟩ := Nat.exists_strictMono α
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

theorem ioo.infinite : Infinite (ioo a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _
#align set.Ioo.infinite Set.ioo.infinite

theorem Ioo_infinite : (ioo a b).Infinite :=
  infinite_coe_iff.1 <| ioo.infinite h
#align set.Ioo_infinite Set.Ioo_infinite

theorem Ico_infinite : (ico a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ico_self
#align set.Ico_infinite Set.Ico_infinite

theorem ico.infinite : Infinite (ico a b) :=
  infinite_coe_iff.2 <| Ico_infinite h
#align set.Ico.infinite Set.ico.infinite

theorem Ioc_infinite : (ioc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ioc_self
#align set.Ioc_infinite Set.Ioc_infinite

theorem ioc.infinite : Infinite (ioc a b) :=
  infinite_coe_iff.2 <| Ioc_infinite h
#align set.Ioc.infinite Set.ioc.infinite

theorem Icc_infinite : (icc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self
#align set.Icc_infinite Set.Icc_infinite

theorem icc.infinite : Infinite (icc a b) :=
  infinite_coe_iff.2 <| Icc_infinite h
#align set.Icc.infinite Set.icc.infinite

end DenselyOrdered

instance [NoMinOrder α] {a : α} : Infinite (iio a) :=
  NoMinOrder.infinite

theorem Iio_infinite [NoMinOrder α] (a : α) : (iio a).Infinite :=
  infinite_coe_iff.1 iio.infinite
#align set.Iio_infinite Set.Iio_infinite

instance [NoMinOrder α] {a : α} : Infinite (iic a) :=
  NoMinOrder.infinite

theorem Iic_infinite [NoMinOrder α] (a : α) : (iic a).Infinite :=
  infinite_coe_iff.1 iic.infinite
#align set.Iic_infinite Set.Iic_infinite

instance [NoMaxOrder α] {a : α} : Infinite (ioi a) :=
  NoMaxOrder.infinite

theorem Ioi_infinite [NoMinOrder α] (a : α) : (iio a).Infinite :=
  infinite_coe_iff.1 iio.infinite
#align set.Ioi_infinite Set.Ioi_infinite

instance [NoMaxOrder α] {a : α} : Infinite (ici a) :=
  NoMaxOrder.infinite

theorem Ici_infinite [NoMaxOrder α] (a : α) : (ici a).Infinite :=
  infinite_coe_iff.1 ici.infinite
#align set.Ici_infinite Set.Ici_infinite

end Set

