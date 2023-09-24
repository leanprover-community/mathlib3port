/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.GroupRingAction.Basic
import GroupTheory.Subgroup.Basic

#align_import algebra.group_ring_action.subobjects from "leanprover-community/mathlib"@"a11f9106a169dd302a285019e5165f8ab32ff433"

/-!
# Instances of `mul_semiring_action` for subobjects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are defined in this file as `semiring`s are not available yet where `submonoid` and `subgroup`
are defined.

Instances for `subsemiring` and `subring` are provided next to the other scalar actions instances
for those subobjects.

-/


variable {M G R : Type _}

variable [Monoid M] [Group G] [Semiring R]

#print Submonoid.mulSemiringAction /-
/-- A stronger version of `submonoid.distrib_mul_action`. -/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) :
    MulSemiringAction H R :=
  { H.MulDistribMulAction, H.DistribMulAction with smul := (· • ·) }
#align submonoid.mul_semiring_action Submonoid.mulSemiringAction
-/

#print Subgroup.mulSemiringAction /-
/-- A stronger version of `subgroup.distrib_mul_action`. -/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) :
    MulSemiringAction H R :=
  H.toSubmonoid.MulSemiringAction
#align subgroup.mul_semiring_action Subgroup.mulSemiringAction
-/

