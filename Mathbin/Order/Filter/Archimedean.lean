/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.archimedean
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Order.Filter.AtTopBot

/-!
# `at_top` filter and archimedean (semi)rings/fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `coe ∘ f : α → R` tends to `at_top` along a filter `l` if and only if so does `f`.
We also prove that `coe : ℕ → R` tends to `at_top` along `at_top`, as well as version of these
two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/


variable {α R : Type _}

open Filter Set

#print Nat.comap_cast_atTop /-
@[simp]
theorem Nat.comap_cast_atTop [StrictOrderedSemiring R] [Archimedean R] :
    comap (coe : ℕ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Nat.cast_le) exists_nat_ge
#align nat.comap_coe_at_top Nat.comap_cast_atTop
-/

#print tendsto_nat_cast_atTop_iff /-
theorem tendsto_nat_cast_atTop_iff [StrictOrderedSemiring R] [Archimedean R] {f : α → ℕ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop :=
  tendsto_atTop_embedding (fun a₁ a₂ => Nat.cast_le) exists_nat_ge
#align tendsto_coe_nat_at_top_iff tendsto_nat_cast_atTop_iff
-/

#print tendsto_nat_cast_atTop_atTop /-
theorem tendsto_nat_cast_atTop_atTop [StrictOrderedSemiring R] [Archimedean R] :
    Tendsto (coe : ℕ → R) atTop atTop :=
  Nat.mono_cast.tendsto_atTop_atTop exists_nat_ge
#align tendsto_coe_nat_at_top_at_top tendsto_nat_cast_atTop_atTop
-/

/- warning: int.comap_coe_at_top -> Int.comap_cast_atTop is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedRing.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R _inst_1)))], Eq.{1} (Filter.{0} Int) (Filter.comap.{0, u1} Int R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R _inst_1)))))))) (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R _inst_1))))) (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedRing.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R _inst_1)))], Eq.{1} (Filter.{0} Int) (Filter.comap.{0, u1} Int R (Int.cast.{u1} R (Ring.toIntCast.{u1} R (StrictOrderedRing.toRing.{u1} R _inst_1))) (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R _inst_1)))) (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))
Case conversion may be inaccurate. Consider using '#align int.comap_coe_at_top Int.comap_cast_atTopₓ'. -/
@[simp]
theorem Int.comap_cast_atTop [StrictOrderedRing R] [Archimedean R] :
    comap (coe : ℤ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r
    ⟨n, by exact_mod_cast hn⟩
#align int.comap_coe_at_top Int.comap_cast_atTop

/- warning: int.comap_coe_at_bot -> Int.comap_cast_atBot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedRing.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R _inst_1)))], Eq.{1} (Filter.{0} Int) (Filter.comap.{0, u1} Int R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R _inst_1)))))))) (Filter.atBot.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R _inst_1))))) (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedRing.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R _inst_1)))], Eq.{1} (Filter.{0} Int) (Filter.comap.{0, u1} Int R (Int.cast.{u1} R (Ring.toIntCast.{u1} R (StrictOrderedRing.toRing.{u1} R _inst_1))) (Filter.atBot.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R _inst_1)))) (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))
Case conversion may be inaccurate. Consider using '#align int.comap_coe_at_bot Int.comap_cast_atBotₓ'. -/
@[simp]
theorem Int.comap_cast_atBot [StrictOrderedRing R] [Archimedean R] :
    comap (coe : ℤ → R) atBot = atBot :=
  comap_embedding_atBot (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le] using hn⟩
#align int.comap_coe_at_bot Int.comap_cast_atBot

/- warning: tendsto_coe_int_at_top_iff -> tendsto_int_cast_atTop_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : StrictOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R _inst_1)))] {f : α -> Int} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u2} α R (fun (n : α) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int R (HasLiftT.mk.{1, succ u2} Int R (CoeTCₓ.coe.{1, succ u2} Int R (Int.castCoe.{u2} R (AddGroupWithOne.toHasIntCast.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R _inst_1))))))) (f n)) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R _inst_1))))) (Filter.Tendsto.{u1, 0} α Int f l (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : StrictOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R _inst_1)))] {f : α -> Int} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u2} α R (fun (n : α) => Int.cast.{u2} R (Ring.toIntCast.{u2} R (StrictOrderedRing.toRing.{u2} R _inst_1)) (f n)) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R _inst_1)))) (Filter.Tendsto.{u1, 0} α Int f l (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))
Case conversion may be inaccurate. Consider using '#align tendsto_coe_int_at_top_iff tendsto_int_cast_atTop_iffₓ'. -/
theorem tendsto_int_cast_atTop_iff [StrictOrderedRing R] [Archimedean R] {f : α → ℤ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop := by
  rw [← tendsto_comap_iff, Int.comap_cast_atTop]
#align tendsto_coe_int_at_top_iff tendsto_int_cast_atTop_iff

/- warning: tendsto_coe_int_at_bot_iff -> tendsto_int_cast_atBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : StrictOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R _inst_1)))] {f : α -> Int} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u2} α R (fun (n : α) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int R (HasLiftT.mk.{1, succ u2} Int R (CoeTCₓ.coe.{1, succ u2} Int R (Int.castCoe.{u2} R (AddGroupWithOne.toHasIntCast.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R _inst_1))))))) (f n)) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R _inst_1))))) (Filter.Tendsto.{u1, 0} α Int f l (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : StrictOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R _inst_1)))] {f : α -> Int} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u2} α R (fun (n : α) => Int.cast.{u2} R (Ring.toIntCast.{u2} R (StrictOrderedRing.toRing.{u2} R _inst_1)) (f n)) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R _inst_1)))) (Filter.Tendsto.{u1, 0} α Int f l (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))
Case conversion may be inaccurate. Consider using '#align tendsto_coe_int_at_bot_iff tendsto_int_cast_atBot_iffₓ'. -/
theorem tendsto_int_cast_atBot_iff [StrictOrderedRing R] [Archimedean R] {f : α → ℤ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atBot ↔ Tendsto f l atBot := by
  rw [← tendsto_comap_iff, Int.comap_cast_atBot]
#align tendsto_coe_int_at_bot_iff tendsto_int_cast_atBot_iff

/- warning: tendsto_coe_int_at_top_at_top -> tendsto_int_cast_atTop_atTop is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedRing.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R _inst_1)))], Filter.Tendsto.{0, u1} Int R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R _inst_1)))))))) (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedRing.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R _inst_1)))], Filter.Tendsto.{0, u1} Int R (Int.cast.{u1} R (Ring.toIntCast.{u1} R (StrictOrderedRing.toRing.{u1} R _inst_1))) (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align tendsto_coe_int_at_top_at_top tendsto_int_cast_atTop_atTopₓ'. -/
theorem tendsto_int_cast_atTop_atTop [StrictOrderedRing R] [Archimedean R] :
    Tendsto (coe : ℤ → R) atTop atTop :=
  Int.cast_mono.tendsto_atTop_atTop fun b =>
    let ⟨n, hn⟩ := exists_nat_ge b
    ⟨n, by exact_mod_cast hn⟩
#align tendsto_coe_int_at_top_at_top tendsto_int_cast_atTop_atTop

/- warning: rat.comap_coe_at_top -> Rat.comap_cast_atTop is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))))))], Eq.{1} (Filter.{0} Rat) (Filter.comap.{0, u1} Rat R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u1} Rat R (CoeTCₓ.coe.{1, succ u1} Rat R (Rat.castCoe.{u1} R (DivisionRing.toHasRatCast.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))))))) (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))) (Filter.atTop.{0} Rat Rat.preorder)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} R (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} R (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} R (LinearOrderedField.toLinearOrderedSemifield.{u1} R _inst_1))))))], Eq.{1} (Filter.{0} Rat) (Filter.comap.{0, u1} Rat R (RatCast.ratCast.{u1} R (LinearOrderedField.toRatCast.{u1} R _inst_1)) (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))))))) (Filter.atTop.{0} Rat Rat.instPreorderRat)
Case conversion may be inaccurate. Consider using '#align rat.comap_coe_at_top Rat.comap_cast_atTopₓ'. -/
@[simp]
theorem Rat.comap_cast_atTop [LinearOrderedField R] [Archimedean R] :
    comap (coe : ℚ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r
    ⟨n, by simpa⟩
#align rat.comap_coe_at_top Rat.comap_cast_atTop

/- warning: rat.comap_coe_at_bot -> Rat.comap_cast_atBot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))))))], Eq.{1} (Filter.{0} Rat) (Filter.comap.{0, u1} Rat R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u1} Rat R (CoeTCₓ.coe.{1, succ u1} Rat R (Rat.castCoe.{u1} R (DivisionRing.toHasRatCast.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))))))) (Filter.atBot.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))) (Filter.atBot.{0} Rat Rat.preorder)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} R (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} R (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} R (LinearOrderedField.toLinearOrderedSemifield.{u1} R _inst_1))))))], Eq.{1} (Filter.{0} Rat) (Filter.comap.{0, u1} Rat R (RatCast.ratCast.{u1} R (LinearOrderedField.toRatCast.{u1} R _inst_1)) (Filter.atBot.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))))))) (Filter.atBot.{0} Rat Rat.instPreorderRat)
Case conversion may be inaccurate. Consider using '#align rat.comap_coe_at_bot Rat.comap_cast_atBotₓ'. -/
@[simp]
theorem Rat.comap_cast_atBot [LinearOrderedField R] [Archimedean R] :
    comap (coe : ℚ → R) atBot = atBot :=
  comap_embedding_atBot (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le] ⟩
#align rat.comap_coe_at_bot Rat.comap_cast_atBot

/- warning: tendsto_coe_rat_at_top_iff -> tendsto_rat_cast_atTop_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R (LinearOrderedField.toLinearOrderedCommRing.{u2} R _inst_1))))))] {f : α -> Rat} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u2} α R (fun (n : α) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u2} Rat R (CoeTCₓ.coe.{1, succ u2} Rat R (Rat.castCoe.{u2} R (DivisionRing.toHasRatCast.{u2} R (Field.toDivisionRing.{u2} R (LinearOrderedField.toField.{u2} R _inst_1)))))) (f n)) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R (LinearOrderedField.toLinearOrderedCommRing.{u2} R _inst_1)))))))) (Filter.Tendsto.{u1, 0} α Rat f l (Filter.atTop.{0} Rat Rat.preorder))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} R (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} R (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} R (LinearOrderedField.toLinearOrderedSemifield.{u2} R _inst_1))))))] {f : α -> Rat} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u2} α R (fun (n : α) => RatCast.ratCast.{u2} R (LinearOrderedField.toRatCast.{u2} R _inst_1) (f n)) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R (LinearOrderedField.toLinearOrderedCommRing.{u2} R _inst_1))))))) (Filter.Tendsto.{u1, 0} α Rat f l (Filter.atTop.{0} Rat Rat.instPreorderRat))
Case conversion may be inaccurate. Consider using '#align tendsto_coe_rat_at_top_iff tendsto_rat_cast_atTop_iffₓ'. -/
theorem tendsto_rat_cast_atTop_iff [LinearOrderedField R] [Archimedean R] {f : α → ℚ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop := by
  rw [← tendsto_comap_iff, Rat.comap_cast_atTop]
#align tendsto_coe_rat_at_top_iff tendsto_rat_cast_atTop_iff

/- warning: tendsto_coe_rat_at_bot_iff -> tendsto_rat_cast_atBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R (LinearOrderedField.toLinearOrderedCommRing.{u2} R _inst_1))))))] {f : α -> Rat} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u2} α R (fun (n : α) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u2} Rat R (CoeTCₓ.coe.{1, succ u2} Rat R (Rat.castCoe.{u2} R (DivisionRing.toHasRatCast.{u2} R (Field.toDivisionRing.{u2} R (LinearOrderedField.toField.{u2} R _inst_1)))))) (f n)) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R (LinearOrderedField.toLinearOrderedCommRing.{u2} R _inst_1)))))))) (Filter.Tendsto.{u1, 0} α Rat f l (Filter.atBot.{0} Rat Rat.preorder))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} R (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} R (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} R (LinearOrderedField.toLinearOrderedSemifield.{u2} R _inst_1))))))] {f : α -> Rat} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u1, u2} α R (fun (n : α) => RatCast.ratCast.{u2} R (LinearOrderedField.toRatCast.{u2} R _inst_1) (f n)) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R (LinearOrderedField.toLinearOrderedCommRing.{u2} R _inst_1))))))) (Filter.Tendsto.{u1, 0} α Rat f l (Filter.atBot.{0} Rat Rat.instPreorderRat))
Case conversion may be inaccurate. Consider using '#align tendsto_coe_rat_at_bot_iff tendsto_rat_cast_atBot_iffₓ'. -/
theorem tendsto_rat_cast_atBot_iff [LinearOrderedField R] [Archimedean R] {f : α → ℚ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atBot ↔ Tendsto f l atBot := by
  rw [← tendsto_comap_iff, Rat.comap_cast_atBot]
#align tendsto_coe_rat_at_bot_iff tendsto_rat_cast_atBot_iff

/- warning: at_top_countable_basis_of_archimedean -> atTop_hasCountableBasis_of_archimedean is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))], Filter.HasCountableBasis.{u1, 0} R Nat (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedCancelAddCommMonoid.toPartialOrder.{u1} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_1))))) (fun (n : Nat) => True) (fun (n : Nat) => Set.Ici.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedCancelAddCommMonoid.toPartialOrder.{u1} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_1))))))))) n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedSemiring.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R _inst_1))], Filter.HasCountableBasis.{u1, 0} R Nat (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R _inst_1))) (fun (n : Nat) => True) (fun (n : Nat) => Set.Ici.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R _inst_1)) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R _inst_1)) n))
Case conversion may be inaccurate. Consider using '#align at_top_countable_basis_of_archimedean atTop_hasCountableBasis_of_archimedeanₓ'. -/
theorem atTop_hasCountableBasis_of_archimedean [LinearOrderedSemiring R] [Archimedean R] :
    (atTop : Filter R).HasCountableBasis (fun n : ℕ => True) fun n => Ici n :=
  { Countable := to_countable _
    to_hasBasis :=
      atTop_basis.to_hasBasis
        (fun x hx =>
          let ⟨n, hn⟩ := exists_nat_ge x
          ⟨n, trivial, Ici_subset_Ici.2 hn⟩)
        fun n hn => ⟨n, trivial, Subset.rfl⟩ }
#align at_top_countable_basis_of_archimedean atTop_hasCountableBasis_of_archimedean

/- warning: at_bot_countable_basis_of_archimedean -> atBot_hasCountableBasis_of_archimedean is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (StrictOrderedRing.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))], Filter.HasCountableBasis.{u1, 0} R Int (Filter.atBot.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))))) (fun (m : Int) => True) (fun (m : Int) => Set.Iic.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StrictOrderedRing.toOrderedAddCommGroup.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))))))) m))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedRing.toLinearOrderedSemiring.{u1} R _inst_1))))], Filter.HasCountableBasis.{u1, 0} R Int (Filter.atBot.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1)))) (fun (m : Int) => True) (fun (m : Int) => Set.Iic.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedRing.toPartialOrder.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))) (Int.cast.{u1} R (Ring.toIntCast.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_1))) m))
Case conversion may be inaccurate. Consider using '#align at_bot_countable_basis_of_archimedean atBot_hasCountableBasis_of_archimedeanₓ'. -/
theorem atBot_hasCountableBasis_of_archimedean [LinearOrderedRing R] [Archimedean R] :
    (atBot : Filter R).HasCountableBasis (fun m : ℤ => True) fun m => Iic m :=
  { Countable := to_countable _
    to_hasBasis :=
      atBot_basis.to_hasBasis
        (fun x hx =>
          let ⟨m, hm⟩ := exists_int_lt x
          ⟨m, trivial, Iic_subset_Iic.2 hm.le⟩)
        fun m hm => ⟨m, trivial, Subset.rfl⟩ }
#align at_bot_countable_basis_of_archimedean atBot_hasCountableBasis_of_archimedean

/- warning: at_top_countably_generated_of_archimedean -> atTop_isCountablyGenerated_of_archimedean is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))], Filter.IsCountablyGenerated.{u1} R (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedCancelAddCommMonoid.toPartialOrder.{u1} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedSemiring.{u1} R] [_inst_2 : Archimedean.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (StrictOrderedSemiring.toOrderedSemiring.{u1} R _inst_1))], Filter.IsCountablyGenerated.{u1} R (Filter.atTop.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align at_top_countably_generated_of_archimedean atTop_isCountablyGenerated_of_archimedeanₓ'. -/
instance (priority := 100) atTop_isCountablyGenerated_of_archimedean [LinearOrderedSemiring R]
    [Archimedean R] : (atTop : Filter R).IsCountablyGenerated :=
  atTop_hasCountableBasis_of_archimedean.IsCountablyGenerated
#align at_top_countably_generated_of_archimedean atTop_isCountablyGenerated_of_archimedean

#print atBot_isCountablyGenerated_of_archimedean /-
instance (priority := 100) atBot_isCountablyGenerated_of_archimedean [LinearOrderedRing R]
    [Archimedean R] : (atBot : Filter R).IsCountablyGenerated :=
  atBot_hasCountableBasis_of_archimedean.IsCountablyGenerated
#align at_bot_countably_generated_of_archimedean atBot_isCountablyGenerated_of_archimedean
-/

namespace Filter

variable {l : Filter α} {f : α → R} {r : R}

section LinearOrderedSemiring

variable [LinearOrderedSemiring R] [Archimedean R]

/- warning: filter.tendsto.const_mul_at_top' -> Filter.Tendsto.const_mul_atTop' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedSemiring.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))))))) r) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))))) r (f x)) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedSemiring.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedSemiring.toPartialOrder.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))))) r) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedSemiring.toPartialOrder.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))))) r (f x)) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedSemiring.toPartialOrder.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.const_mul_at_top' Filter.Tendsto.const_mul_atTop'ₓ'. -/
/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.const_mul_at_top`). -/
theorem Tendsto.const_mul_atTop' (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop :=
  by
  apply tendsto_at_top.2 fun b => _
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr
  rw [nsmul_eq_mul'] at hn
  filter_upwards [tendsto_at_top.1 hf (n * max b 0)]with x hx
  calc
    b ≤ 1 * max b 0 := by
      rw [one_mul]
      exact le_max_left _ _
    _ ≤ r * n * max b 0 := mul_le_mul_of_nonneg_right hn (le_max_right _ _)
    _ = r * (n * max b 0) := by rw [mul_assoc]
    _ ≤ r * f x := mul_le_mul_of_nonneg_left hx (le_of_lt hr)
    
#align filter.tendsto.const_mul_at_top' Filter.Tendsto.const_mul_atTop'

/- warning: filter.tendsto.at_top_mul_const' -> Filter.Tendsto.atTop_mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedSemiring.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))))))) r) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedSemiring.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedSemiring.toPartialOrder.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))))) r) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedSemiring.toPartialOrder.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedSemiring.toPartialOrder.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_top_mul_const' Filter.Tendsto.atTop_mul_const'ₓ'. -/
/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `filter.tendsto.at_top_mul_const`). -/
theorem Tendsto.atTop_mul_const' (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop :=
  by
  apply tendsto_at_top.2 fun b => _
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr
  have hn' : 1 ≤ (n : R) * r := by rwa [nsmul_eq_mul] at hn
  filter_upwards [tendsto_at_top.1 hf (max b 0 * n)]with x hx
  calc
    b ≤ max b 0 * 1 := by
      rw [mul_one]
      exact le_max_left _ _
    _ ≤ max b 0 * (n * r) := mul_le_mul_of_nonneg_left hn' (le_max_right _ _)
    _ = max b 0 * n * r := by rw [mul_assoc]
    _ ≤ f x * r := mul_le_mul_of_nonneg_right hx (le_of_lt hr)
    
#align filter.tendsto.at_top_mul_const' Filter.Tendsto.atTop_mul_const'

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing R] [Archimedean R]

/- warning: filter.tendsto.at_top_mul_neg_const' -> Filter.Tendsto.atTop_mul_neg_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) r (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))))))))) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toLinearOrderedSemiring.{u2} R _inst_1))))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))) r (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toLinearOrderedSemiring.{u2} R _inst_1)))))))) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_top_mul_neg_const' Filter.Tendsto.atTop_mul_neg_const'ₓ'. -/
/-- See also `filter.tendsto.at_top_mul_neg_const` for a version of this lemma for
`linear_ordered_field`s which does not require the `archimedean` assumption. -/
theorem Tendsto.atTop_mul_neg_const' (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot := by
  simpa only [tendsto_neg_at_top_iff, mul_neg] using hf.at_top_mul_const' (neg_pos.mpr hr)
#align filter.tendsto.at_top_mul_neg_const' Filter.Tendsto.atTop_mul_neg_const'

/- warning: filter.tendsto.at_bot_mul_const' -> Filter.Tendsto.atBot_mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))))))) r) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toLinearOrderedSemiring.{u2} R _inst_1))))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toLinearOrderedSemiring.{u2} R _inst_1))))))) r) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_bot_mul_const' Filter.Tendsto.atBot_mul_const'ₓ'. -/
/-- See also `filter.tendsto.at_bot_mul_const` for a version of this lemma for
`linear_ordered_field`s which does not require the `archimedean` assumption. -/
theorem Tendsto.atBot_mul_const' (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot :=
  by
  simp only [← tendsto_neg_at_top_iff, ← neg_mul] at hf⊢
  exact hf.at_top_mul_const' hr
#align filter.tendsto.at_bot_mul_const' Filter.Tendsto.atBot_mul_const'

/- warning: filter.tendsto.at_bot_mul_neg_const' -> Filter.Tendsto.atBot_mul_neg_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (StrictOrderedRing.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) r (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))))))))) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (StrictOrderedRing.toOrderedAddCommGroup.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {f : α -> R} {r : R} [_inst_1 : LinearOrderedRing.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (StrictOrderedSemiring.toOrderedSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toLinearOrderedSemiring.{u2} R _inst_1))))], (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))) r (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} R (LinearOrderedRing.toLinearOrderedSemiring.{u2} R _inst_1)))))))) -> (Filter.Tendsto.{u1, u2} α R f l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocRing.toMul.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (StrictOrderedRing.toPartialOrder.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_bot_mul_neg_const' Filter.Tendsto.atBot_mul_neg_const'ₓ'. -/
/-- See also `filter.tendsto.at_bot_mul_neg_const` for a version of this lemma for
`linear_ordered_field`s which does not require the `archimedean` assumption. -/
theorem Tendsto.atBot_mul_neg_const' (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop := by
  simpa only [mul_neg, tendsto_neg_at_bot_iff] using hf.at_bot_mul_const' (neg_pos.2 hr)
#align filter.tendsto.at_bot_mul_neg_const' Filter.Tendsto.atBot_mul_neg_const'

end LinearOrderedRing

section LinearOrderedCancelAddCommMonoid

variable [LinearOrderedCancelAddCommMonoid R] [Archimedean R]

/- warning: filter.tendsto.at_top_nsmul_const -> Filter.Tendsto.atTop_nsmul_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedCancelAddCommMonoid.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1))] {f : α -> Nat}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R (AddCancelMonoid.toAddRightCancelMonoid.{u2} R (AddCancelCommMonoid.toAddCancelMonoid.{u2} R (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1)))))))))) r) -> (Filter.Tendsto.{u1, 0} α Nat f l (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => SMul.smul.{0, u2} Nat R (AddMonoid.SMul.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R (AddCancelMonoid.toAddRightCancelMonoid.{u2} R (AddCancelCommMonoid.toAddCancelMonoid.{u2} R (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1)))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedCancelAddCommMonoid.{u2} R] [_inst_2 : Archimedean.{u2} R (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} R _inst_1))] {f : α -> Nat}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (AddRightCancelMonoid.toZero.{u2} R (AddCancelMonoid.toAddRightCancelMonoid.{u2} R (AddCancelCommMonoid.toAddCancelMonoid.{u2} R (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1))))))) r) -> (Filter.Tendsto.{u1, 0} α Nat f l (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HSMul.hSMul.{0, u2, u2} Nat R R (instHSMul.{0, u2} Nat R (AddMonoid.SMul.{u2} R (AddRightCancelMonoid.toAddMonoid.{u2} R (AddCancelMonoid.toAddRightCancelMonoid.{u2} R (AddCancelCommMonoid.toAddCancelMonoid.{u2} R (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1))))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_top_nsmul_const Filter.Tendsto.atTop_nsmul_constₓ'. -/
theorem Tendsto.atTop_nsmul_const {f : α → ℕ} (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atTop :=
  by
  refine' tendsto_at_top.mpr fun s => _
  obtain ⟨n : ℕ, hn : s ≤ n • r⟩ := Archimedean.arch s hr
  exact (tendsto_at_top.mp hf n).mono fun a ha => hn.trans (nsmul_le_nsmul hr.le ha)
#align filter.tendsto.at_top_nsmul_const Filter.Tendsto.atTop_nsmul_const

end LinearOrderedCancelAddCommMonoid

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup R] [Archimedean R]

/- warning: filter.tendsto.at_top_nsmul_neg_const -> Filter.Tendsto.atTop_nsmul_neg_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} R (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))] {f : α -> Nat}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) r (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))))))))) -> (Filter.Tendsto.{u1, 0} α Nat f l (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => SMul.smul.{0, u2} Nat R (AddMonoid.SMul.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} R _inst_1)))] {f : α -> Nat}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) r (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (SubtractionCommMonoid.toSubtractionMonoid.{u2} R (AddCommGroup.toDivisionAddCommMonoid.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))))))) -> (Filter.Tendsto.{u1, 0} α Nat f l (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HSMul.hSMul.{0, u2, u2} Nat R R (instHSMul.{0, u2} Nat R (AddMonoid.SMul.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_top_nsmul_neg_const Filter.Tendsto.atTop_nsmul_neg_constₓ'. -/
theorem Tendsto.atTop_nsmul_neg_const {f : α → ℕ} (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atBot := by simpa using hf.at_top_nsmul_const (neg_pos.2 hr)
#align filter.tendsto.at_top_nsmul_neg_const Filter.Tendsto.atTop_nsmul_neg_const

/- warning: filter.tendsto.at_top_zsmul_const -> Filter.Tendsto.atTop_zsmul_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} R (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))] {f : α -> Int}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))))))) r) -> (Filter.Tendsto.{u1, 0} α Int f l (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => SMul.smul.{0, u2} Int R (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} R _inst_1)))] {f : α -> Int}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (SubtractionCommMonoid.toSubtractionMonoid.{u2} R (AddCommGroup.toDivisionAddCommMonoid.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))))))) r) -> (Filter.Tendsto.{u1, 0} α Int f l (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HSMul.hSMul.{0, u2, u2} Int R R (instHSMul.{0, u2} Int R (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_top_zsmul_const Filter.Tendsto.atTop_zsmul_constₓ'. -/
theorem Tendsto.atTop_zsmul_const {f : α → ℤ} (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atTop :=
  by
  refine' tendsto_at_top.mpr fun s => _
  obtain ⟨n : ℕ, hn : s ≤ n • r⟩ := Archimedean.arch s hr
  replace hn : s ≤ (n : ℤ) • r; · simpa
  exact (tendsto_at_top.mp hf n).mono fun a ha => hn.trans (zsmul_le_zsmul hr.le ha)
#align filter.tendsto.at_top_zsmul_const Filter.Tendsto.atTop_zsmul_const

/- warning: filter.tendsto.at_top_zsmul_neg_const -> Filter.Tendsto.atTop_zsmul_neg_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} R (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))] {f : α -> Int}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) r (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))))))))) -> (Filter.Tendsto.{u1, 0} α Int f l (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => SMul.smul.{0, u2} Int R (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} R _inst_1)))] {f : α -> Int}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) r (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (SubtractionCommMonoid.toSubtractionMonoid.{u2} R (AddCommGroup.toDivisionAddCommMonoid.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))))))) -> (Filter.Tendsto.{u1, 0} α Int f l (Filter.atTop.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HSMul.hSMul.{0, u2, u2} Int R R (instHSMul.{0, u2} Int R (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_top_zsmul_neg_const Filter.Tendsto.atTop_zsmul_neg_constₓ'. -/
theorem Tendsto.atTop_zsmul_neg_const {f : α → ℤ} (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atBot := by simpa using hf.at_top_zsmul_const (neg_pos.2 hr)
#align filter.tendsto.at_top_zsmul_neg_const Filter.Tendsto.atTop_zsmul_neg_const

/- warning: filter.tendsto.at_bot_zsmul_const -> Filter.Tendsto.atBot_zsmul_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} R (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))] {f : α -> Int}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))))))) r) -> (Filter.Tendsto.{u1, 0} α Int f l (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => SMul.smul.{0, u2} Int R (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} R _inst_1)))] {f : α -> Int}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (SubtractionCommMonoid.toSubtractionMonoid.{u2} R (AddCommGroup.toDivisionAddCommMonoid.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))))))) r) -> (Filter.Tendsto.{u1, 0} α Int f l (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HSMul.hSMul.{0, u2, u2} Int R R (instHSMul.{0, u2} Int R (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))) (f x) r) l (Filter.atBot.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_bot_zsmul_const Filter.Tendsto.atBot_zsmul_constₓ'. -/
theorem Tendsto.atBot_zsmul_const {f : α → ℤ} (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x • r) l atBot :=
  by
  simp only [← tendsto_neg_at_top_iff, ← neg_zsmul] at hf⊢
  exact hf.at_top_zsmul_const hr
#align filter.tendsto.at_bot_zsmul_const Filter.Tendsto.atBot_zsmul_const

/- warning: filter.tendsto.at_bot_zsmul_neg_const -> Filter.Tendsto.atBot_zsmul_neg_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} R (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))] {f : α -> Int}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) r (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))))))))) -> (Filter.Tendsto.{u1, 0} α Int f l (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => SMul.smul.{0, u2} Int R (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} {l : Filter.{u1} α} {r : R} [_inst_1 : LinearOrderedAddCommGroup.{u2} R] [_inst_2 : Archimedean.{u2} R (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} R (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} R (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} R _inst_1)))] {f : α -> Int}, (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))) r (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (NegZeroClass.toZero.{u2} R (SubNegZeroMonoid.toNegZeroClass.{u2} R (SubtractionMonoid.toSubNegZeroMonoid.{u2} R (SubtractionCommMonoid.toSubtractionMonoid.{u2} R (AddCommGroup.toDivisionAddCommMonoid.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))))))) -> (Filter.Tendsto.{u1, 0} α Int f l (Filter.atBot.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) -> (Filter.Tendsto.{u1, u2} α R (fun (x : α) => HSMul.hSMul.{0, u2, u2} Int R R (instHSMul.{0, u2} Int R (SubNegMonoid.SMulInt.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (OrderedAddCommGroup.toAddCommGroup.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))) (f x) r) l (Filter.atTop.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommGroup.toPartialOrder.{u2} R (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.at_bot_zsmul_neg_const Filter.Tendsto.atBot_zsmul_neg_constₓ'. -/
theorem Tendsto.atBot_zsmul_neg_const {f : α → ℤ} (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x • r) l atTop := by simpa using hf.at_bot_zsmul_const (neg_pos.2 hr)
#align filter.tendsto.at_bot_zsmul_neg_const Filter.Tendsto.atBot_zsmul_neg_const

end LinearOrderedAddCommGroup

end Filter

