/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

! This file was ported from Lean 3 source module data.set.intervals.infinite
! leanprover-community/mathlib commit 4d392a6c9c4539cbeca399b3ee0afea398fbd2eb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Finite

/-!
# Infinitude of intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/


variable {α : Type _} [Preorder α]

/- warning: no_max_order.infinite -> NoMaxOrder.infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Nonempty.{succ u1} α] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], Infinite.{succ u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Nonempty.{succ u1} α] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], Infinite.{succ u1} α
Case conversion may be inaccurate. Consider using '#align no_max_order.infinite NoMaxOrder.infiniteₓ'. -/
/-- A nonempty preorder with no maximal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
theorem NoMaxOrder.infinite [Nonempty α] [NoMaxOrder α] : Infinite α :=
  let ⟨f, hf⟩ := Nat.exists_strictMono α
  Infinite.of_injective f hf.Injective
#align no_max_order.infinite NoMaxOrder.infinite

/- warning: no_min_order.infinite -> NoMinOrder.infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Nonempty.{succ u1} α] [_inst_3 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)], Infinite.{succ u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Nonempty.{succ u1} α] [_inst_3 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)], Infinite.{succ u1} α
Case conversion may be inaccurate. Consider using '#align no_min_order.infinite NoMinOrder.infiniteₓ'. -/
/-- A nonempty preorder with no minimal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
theorem NoMinOrder.infinite [Nonempty α] [NoMinOrder α] : Infinite α :=
  @NoMaxOrder.infinite αᵒᵈ _ _ _
#align no_min_order.infinite NoMinOrder.infinite

namespace Set

section DenselyOrdered

variable [DenselyOrdered α] {a b : α} (h : a < b)

/- warning: set.Ioo.infinite -> Set.Ioo.infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Infinite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ioo.{u1} α _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Infinite.{succ u1} (Set.Elem.{u1} α (Set.Ioo.{u1} α _inst_1 a b)))
Case conversion may be inaccurate. Consider using '#align set.Ioo.infinite Set.Ioo.infiniteₓ'. -/
theorem Ioo.infinite : Infinite (Ioo a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _
#align set.Ioo.infinite Set.Ioo.infinite

/- warning: set.Ioo_infinite -> Set.Ioo_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Set.Infinite.{u1} α (Set.Ioo.{u1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Set.Infinite.{u1} α (Set.Ioo.{u1} α _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align set.Ioo_infinite Set.Ioo_infiniteₓ'. -/
theorem Ioo_infinite : (Ioo a b).Infinite :=
  infinite_coe_iff.1 <| Ioo.infinite h
#align set.Ioo_infinite Set.Ioo_infinite

/- warning: set.Ico_infinite -> Set.Ico_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Set.Infinite.{u1} α (Set.Ico.{u1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Set.Infinite.{u1} α (Set.Ico.{u1} α _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align set.Ico_infinite Set.Ico_infiniteₓ'. -/
theorem Ico_infinite : (Ico a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ico_self
#align set.Ico_infinite Set.Ico_infinite

/- warning: set.Ico.infinite -> Set.Ico.infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Infinite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ico.{u1} α _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Infinite.{succ u1} (Set.Elem.{u1} α (Set.Ico.{u1} α _inst_1 a b)))
Case conversion may be inaccurate. Consider using '#align set.Ico.infinite Set.Ico.infiniteₓ'. -/
theorem Ico.infinite : Infinite (Ico a b) :=
  infinite_coe_iff.2 <| Ico_infinite h
#align set.Ico.infinite Set.Ico.infinite

/- warning: set.Ioc_infinite -> Set.Ioc_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Set.Infinite.{u1} α (Set.Ioc.{u1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Set.Infinite.{u1} α (Set.Ioc.{u1} α _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align set.Ioc_infinite Set.Ioc_infiniteₓ'. -/
theorem Ioc_infinite : (Ioc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ioc_self
#align set.Ioc_infinite Set.Ioc_infinite

/- warning: set.Ioc.infinite -> Set.Ioc.infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Infinite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Ioc.{u1} α _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Infinite.{succ u1} (Set.Elem.{u1} α (Set.Ioc.{u1} α _inst_1 a b)))
Case conversion may be inaccurate. Consider using '#align set.Ioc.infinite Set.Ioc.infiniteₓ'. -/
theorem Ioc.infinite : Infinite (Ioc a b) :=
  infinite_coe_iff.2 <| Ioc_infinite h
#align set.Ioc.infinite Set.Ioc.infinite

/- warning: set.Icc_infinite -> Set.Icc_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Set.Infinite.{u1} α (Set.Icc.{u1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Set.Infinite.{u1} α (Set.Icc.{u1} α _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align set.Icc_infinite Set.Icc_infiniteₓ'. -/
theorem Icc_infinite : (Icc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self
#align set.Icc_infinite Set.Icc_infinite

/- warning: set.Icc.infinite -> Set.Icc.infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b) -> (Infinite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Icc.{u1} α _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α _inst_1)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Infinite.{succ u1} (Set.Elem.{u1} α (Set.Icc.{u1} α _inst_1 a b)))
Case conversion may be inaccurate. Consider using '#align set.Icc.infinite Set.Icc.infiniteₓ'. -/
theorem Icc.infinite : Infinite (Icc a b) :=
  infinite_coe_iff.2 <| Icc_infinite h
#align set.Icc.infinite Set.Icc.infinite

end DenselyOrdered

instance [NoMinOrder α] {a : α} : Infinite (Iio a) :=
  NoMinOrder.infinite

/- warning: set.Iio_infinite -> Set.Iio_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] (a : α), Set.Infinite.{u1} α (Set.Iio.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)] (a : α), Set.Infinite.{u1} α (Set.Iio.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align set.Iio_infinite Set.Iio_infiniteₓ'. -/
theorem Iio_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite :=
  infinite_coe_iff.1 Iio.infinite
#align set.Iio_infinite Set.Iio_infinite

instance [NoMinOrder α] {a : α} : Infinite (Iic a) :=
  NoMinOrder.infinite

/- warning: set.Iic_infinite -> Set.Iic_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] (a : α), Set.Infinite.{u1} α (Set.Iic.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)] (a : α), Set.Infinite.{u1} α (Set.Iic.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align set.Iic_infinite Set.Iic_infiniteₓ'. -/
theorem Iic_infinite [NoMinOrder α] (a : α) : (Iic a).Infinite :=
  infinite_coe_iff.1 Iic.infinite
#align set.Iic_infinite Set.Iic_infinite

instance [NoMaxOrder α] {a : α} : Infinite (Ioi a) :=
  NoMaxOrder.infinite

/- warning: set.Ioi_infinite -> Set.Ioi_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] (a : α), Set.Infinite.{u1} α (Set.Ioi.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)] (a : α), Set.Infinite.{u1} α (Set.Ioi.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align set.Ioi_infinite Set.Ioi_infiniteₓ'. -/
theorem Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite :=
  infinite_coe_iff.1 Ioi.infinite
#align set.Ioi_infinite Set.Ioi_infinite

instance [NoMaxOrder α] {a : α} : Infinite (Ici a) :=
  NoMaxOrder.infinite

/- warning: set.Ici_infinite -> Set.Ici_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α _inst_1)] (a : α), Set.Infinite.{u1} α (Set.Ici.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α _inst_1)] (a : α), Set.Infinite.{u1} α (Set.Ici.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align set.Ici_infinite Set.Ici_infiniteₓ'. -/
theorem Ici_infinite [NoMaxOrder α] (a : α) : (Ici a).Infinite :=
  infinite_coe_iff.1 Ici.infinite
#align set.Ici_infinite Set.Ici_infinite

end Set

