/-
Copyright (c) 2020 Heather Macbeth, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot

! This file was ported from Lean 3 source module group_theory.archimedean
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Archimedean
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Archimedean groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves a few facts about ordered groups which satisfy the `archimedean` property, that is:
`class archimedean (α) [ordered_add_comm_monoid α] : Prop :=`
`(arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n • y)`

They are placed here in a separate file (rather than incorporated as a continuation of
`algebra.order.archimedean`) because they rely on some imports from `group_theory` -- bundled
subgroups in particular.

The main result is `add_subgroup.cyclic_of_min`:  a subgroup of a decidable archimedean abelian
group is cyclic, if its set of positive elements has a minimal element.

This result is used in this file to deduce `int.subgroup_cyclic`, proving that every subgroup of `ℤ`
is cyclic.  (There are several other methods one could use to prove this fact, including more purely
algebraic methods, but none seem to exist in mathlib as of writing.  The closest is
`subgroup.is_cyclic`, but that has not been transferred to `add_subgroup`.)

The result is also used in `topology.instances.real` as an ingredient in the classification of
subgroups of `ℝ`.
-/


variable {G : Type _} [LinearOrderedAddCommGroup G] [Archimedean G]

open LinearOrderedAddCommGroup

/- warning: add_subgroup.cyclic_of_min -> AddSubgroup.cyclic_of_min is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u1} G] [_inst_2 : Archimedean.{u1} G (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} G (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))] {H : AddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))} {a : G}, (IsLeast.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1))) (setOf.{u1} G (fun (g : G) => And (Membership.Mem.{u1, u1} G (AddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))) G (AddSubgroup.setLike.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1))))) g H) (LT.lt.{u1} G (Preorder.toLT.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))))))))) g))) a) -> (Eq.{succ u1} (AddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))) H (AddSubgroup.closure.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1))) (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.hasSingleton.{u1} G) a)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u1} G] [_inst_2 : Archimedean.{u1} G (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} G (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u1} G (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u1} G _inst_1)))] {H : AddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))} {a : G}, (IsLeast.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1))) (setOf.{u1} G (fun (g : G) => And (Membership.mem.{u1, u1} G (AddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))) G (AddSubgroup.instSetLikeAddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1))))) g H) (LT.lt.{u1} G (Preorder.toLT.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))) (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1))))))))) g))) a) -> (Eq.{succ u1} (AddSubgroup.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1)))) H (AddSubgroup.closure.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} G _inst_1))) (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.instSingletonSet.{u1} G) a)))
Case conversion may be inaccurate. Consider using '#align add_subgroup.cyclic_of_min AddSubgroup.cyclic_of_minₓ'. -/
/-- Given a subgroup `H` of a decidable linearly ordered archimedean abelian group `G`, if there
exists a minimal element `a` of `H ∩ G_{>0}` then `H` is generated by `a`. -/
theorem AddSubgroup.cyclic_of_min {H : AddSubgroup G} {a : G}
    (ha : IsLeast { g : G | g ∈ H ∧ 0 < g } a) : H = AddSubgroup.closure {a} :=
  by
  obtain ⟨⟨a_in, a_pos⟩, a_min⟩ := ha
  refine' le_antisymm _ (H.closure_le.mpr <| by simp [a_in])
  intro g g_in
  obtain ⟨k, ⟨nonneg, lt⟩, _⟩ : ∃! k, 0 ≤ g - k • a ∧ g - k • a < a :=
    existsUnique_zsmul_near_of_pos' a_pos g
  have h_zero : g - k • a = 0 := by
    by_contra h
    have h : a ≤ g - k • a := by
      refine' a_min ⟨_, _⟩
      · exact AddSubgroup.sub_mem H g_in (AddSubgroup.zsmul_mem H a_in k)
      · exact lt_of_le_of_ne nonneg (Ne.symm h)
    have h' : ¬a ≤ g - k • a := not_le.mpr lt
    contradiction
  simp [sub_eq_zero.mp h_zero, AddSubgroup.mem_closure_singleton]
#align add_subgroup.cyclic_of_min AddSubgroup.cyclic_of_min

/- warning: int.subgroup_cyclic -> Int.subgroup_cyclic is a dubious translation:
lean 3 declaration is
  forall (H : AddSubgroup.{0} Int Int.addGroup), Exists.{1} Int (fun (a : Int) => Eq.{1} (AddSubgroup.{0} Int Int.addGroup) H (AddSubgroup.closure.{0} Int Int.addGroup (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a)))
but is expected to have type
  forall (H : AddSubgroup.{0} Int Int.instAddGroupInt), Exists.{1} Int (fun (a : Int) => Eq.{1} (AddSubgroup.{0} Int Int.instAddGroupInt) H (AddSubgroup.closure.{0} Int Int.instAddGroupInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a)))
Case conversion may be inaccurate. Consider using '#align int.subgroup_cyclic Int.subgroup_cyclicₓ'. -/
/-- Every subgroup of `ℤ` is cyclic. -/
theorem Int.subgroup_cyclic (H : AddSubgroup ℤ) : ∃ a, H = AddSubgroup.closure {a} :=
  by
  cases' AddSubgroup.bot_or_exists_ne_zero H with h h
  · use 0
    rw [h]
    exact add_subgroup.closure_singleton_zero.symm
  let s := { g : ℤ | g ∈ H ∧ 0 < g }
  have h_bdd : ∀ g ∈ s, (0 : ℤ) ≤ g := fun _ h => le_of_lt h.2
  obtain ⟨g₀, g₀_in, g₀_ne⟩ := h
  obtain ⟨g₁, g₁_in, g₁_pos⟩ : ∃ g₁ : ℤ, g₁ ∈ H ∧ 0 < g₁ :=
    by
    cases' lt_or_gt_of_ne g₀_ne with Hg₀ Hg₀
    · exact ⟨-g₀, H.neg_mem g₀_in, neg_pos.mpr Hg₀⟩
    · exact ⟨g₀, g₀_in, Hg₀⟩
  obtain ⟨a, ha, ha'⟩ := Int.exists_least_of_bdd ⟨(0 : ℤ), h_bdd⟩ ⟨g₁, g₁_in, g₁_pos⟩
  exact ⟨a, AddSubgroup.cyclic_of_min ⟨ha, ha'⟩⟩
#align int.subgroup_cyclic Int.subgroup_cyclic

