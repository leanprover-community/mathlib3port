/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import GroupTheory.Subgroup.Basic

#align_import group_theory.subgroup.actions from "leanprover-community/mathlib"@"a11f9106a169dd302a285019e5165f8ab32ff433"

/-!
# Actions by `subgroup`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are just copies of the definitions about `submonoid` starting from `submonoid.mul_action`.

## Tags
subgroup, subgroups

-/


namespace Subgroup

variable {G : Type _} [Group G]

variable {α β : Type _}

/-- The action by a subgroup is the action by the underlying group. -/
@[to_additive "The additive action by an add_subgroup is the action by the underlying\nadd_group. "]
instance [MulAction G α] (S : Subgroup G) : MulAction S α :=
  S.toSubmonoid.MulAction

#print Subgroup.smul_def /-
@[to_additive]
theorem smul_def [MulAction G α] {S : Subgroup G} (g : S) (m : α) : g • m = (g : G) • m :=
  rfl
#align subgroup.smul_def Subgroup.smul_def
#align add_subgroup.vadd_def AddSubgroup.vadd_def
-/

#print Subgroup.smulCommClass_left /-
@[to_additive]
instance smulCommClass_left [MulAction G β] [SMul α β] [SMulCommClass G α β] (S : Subgroup G) :
    SMulCommClass S α β :=
  S.toSubmonoid.smulCommClass_left
#align subgroup.smul_comm_class_left Subgroup.smulCommClass_left
#align add_subgroup.vadd_comm_class_left AddSubgroup.vaddCommClass_left
-/

#print Subgroup.smulCommClass_right /-
@[to_additive]
instance smulCommClass_right [SMul α β] [MulAction G β] [SMulCommClass α G β] (S : Subgroup G) :
    SMulCommClass α S β :=
  S.toSubmonoid.smulCommClass_right
#align subgroup.smul_comm_class_right Subgroup.smulCommClass_right
#align add_subgroup.vadd_comm_class_right AddSubgroup.vaddCommClass_right
-/

/-- Note that this provides `is_scalar_tower S G G` which is needed by `smul_mul_assoc`. -/
instance [SMul α β] [MulAction G α] [MulAction G β] [IsScalarTower G α β] (S : Subgroup G) :
    IsScalarTower S α β :=
  S.toSubmonoid.IsScalarTower

instance [MulAction G α] [FaithfulSMul G α] (S : Subgroup G) : FaithfulSMul S α :=
  S.toSubmonoid.FaithfulSMul

/-- The action by a subgroup is the action by the underlying group. -/
instance [AddMonoid α] [DistribMulAction G α] (S : Subgroup G) : DistribMulAction S α :=
  S.toSubmonoid.DistribMulAction

/-- The action by a subgroup is the action by the underlying group. -/
instance [Monoid α] [MulDistribMulAction G α] (S : Subgroup G) : MulDistribMulAction S α :=
  S.toSubmonoid.MulDistribMulAction

#print Subgroup.center.smulCommClass_left /-
/-- The center of a group acts commutatively on that group. -/
instance center.smulCommClass_left : SMulCommClass (center G) G G :=
  Submonoid.center.smulCommClass_left
#align subgroup.center.smul_comm_class_left Subgroup.center.smulCommClass_left
-/

#print Subgroup.center.smulCommClass_right /-
/-- The center of a group acts commutatively on that group. -/
instance center.smulCommClass_right : SMulCommClass G (center G) G :=
  Submonoid.center.smulCommClass_right
#align subgroup.center.smul_comm_class_right Subgroup.center.smulCommClass_right
-/

end Subgroup

