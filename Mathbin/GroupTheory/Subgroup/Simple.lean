/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module group_theory.subgroup.simple
! leanprover-community/mathlib commit fac369018417f980cec5fcdafc766a69f88d8cfe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Actions

/-!
# Simple groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `is_simple_group G`, a class indicating that a group has exactly two normal
subgroups.

## Main definitions

- `is_simple_group G`, a class indicating that a group has exactly two normal subgroups.

## Tags
subgroup, subgroups

-/


variable {G : Type _} [Group G]

variable {A : Type _} [AddGroup A]

section

variable (G) (A)

#print IsSimpleGroup /-
/-- A `group` is simple when it has exactly two normal `subgroup`s. -/
class IsSimpleGroup extends Nontrivial G : Prop where
  eq_bot_or_eq_top_of_normal : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤
#align is_simple_group IsSimpleGroup
-/

#print IsSimpleAddGroup /-
/-- An `add_group` is simple when it has exactly two normal `add_subgroup`s. -/
class IsSimpleAddGroup extends Nontrivial A : Prop where
  eq_bot_or_eq_top_of_normal : ∀ H : AddSubgroup A, H.Normal → H = ⊥ ∨ H = ⊤
#align is_simple_add_group IsSimpleAddGroup
-/

attribute [to_additive] IsSimpleGroup

variable {G} {A}

/- warning: subgroup.normal.eq_bot_or_eq_top -> Subgroup.Normal.eq_bot_or_eq_top is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_3 : IsSimpleGroup.{u1} G _inst_1] {H : Subgroup.{u1} G _inst_1}, (Subgroup.Normal.{u1} G _inst_1 H) -> (Or (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1))) (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_3 : IsSimpleGroup.{u1} G _inst_1] {H : Subgroup.{u1} G _inst_1}, (Subgroup.Normal.{u1} G _inst_1 H) -> (Or (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1))) (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align subgroup.normal.eq_bot_or_eq_top Subgroup.Normal.eq_bot_or_eq_topₓ'. -/
@[to_additive]
theorem Subgroup.Normal.eq_bot_or_eq_top [IsSimpleGroup G] {H : Subgroup G} (Hn : H.Normal) :
    H = ⊥ ∨ H = ⊤ :=
  IsSimpleGroup.eq_bot_or_eq_top_of_normal H Hn
#align subgroup.normal.eq_bot_or_eq_top Subgroup.Normal.eq_bot_or_eq_top
#align add_subgroup.normal.eq_bot_or_eq_top AddSubgroup.Normal.eq_bot_or_eq_top

namespace IsSimpleGroup

@[to_additive]
instance {C : Type _} [CommGroup C] [IsSimpleGroup C] : IsSimpleOrder (Subgroup C) :=
  ⟨fun H => H.normal_of_comm.eq_bot_or_eq_top⟩

open _Root_.Subgroup

/- warning: is_simple_group.is_simple_group_of_surjective -> IsSimpleGroup.isSimpleGroup_of_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] [_inst_4 : IsSimpleGroup.{u1} G _inst_1] [_inst_5 : Nontrivial.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))), (Function.Surjective.{succ u1, succ u2} G H (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) f)) -> (IsSimpleGroup.{u2} H _inst_3)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] [_inst_4 : IsSimpleGroup.{u1} G _inst_1] [_inst_5 : Nontrivial.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))), (Function.Surjective.{succ u1, succ u2} G H (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => H) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))))) f)) -> (IsSimpleGroup.{u2} H _inst_3)
Case conversion may be inaccurate. Consider using '#align is_simple_group.is_simple_group_of_surjective IsSimpleGroup.isSimpleGroup_of_surjectiveₓ'. -/
@[to_additive]
theorem isSimpleGroup_of_surjective {H : Type _} [Group H] [IsSimpleGroup G] [Nontrivial H]
    (f : G →* H) (hf : Function.Surjective f) : IsSimpleGroup H :=
  ⟨Nontrivial.exists_pair_ne, fun H iH =>
    by
    refine' (iH.comap f).eq_bot_or_eq_top.imp (fun h => _) fun h => _
    · rw [← map_bot f, ← h, map_comap_eq_self_of_surjective hf]
    · rw [← comap_top f] at h; exact comap_injective hf h⟩
#align is_simple_group.is_simple_group_of_surjective IsSimpleGroup.isSimpleGroup_of_surjective
#align is_simple_add_group.is_simple_add_group_of_surjective IsSimpleAddGroup.isSimpleAddGroup_of_surjective

end IsSimpleGroup

end

