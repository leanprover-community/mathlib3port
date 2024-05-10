/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich
-/
import Algebra.Group.Subgroup.Actions

#align_import group_theory.subgroup.mul_opposite from "leanprover-community/mathlib"@"a11f9106a169dd302a285019e5165f8ab32ff433"

/-!
# Mul-opposite subgroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Tags
subgroup, subgroups

-/


variable {G : Type _} [Group G]

namespace Subgroup

#print Subgroup.opEquiv /-
/-- A subgroup `H` of `G` determines a subgroup `H.opposite` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive
      "An additive subgroup `H` of `G` determines an additive subgroup `H.opposite` of the\n  opposite additive group `Gᵃᵒᵖ`."]
def opEquiv : Subgroup G ≃ Subgroup Gᵐᵒᵖ
    where
  toFun H :=
    { carrier := MulOpposite.unop ⁻¹' (H : Set G)
      one_mem' := H.one_mem
      hMul_mem' := fun a b ha hb => H.hMul_mem hb ha
      inv_mem' := fun a => H.inv_mem }
  invFun H :=
    { carrier := MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
      one_mem' := H.one_mem
      hMul_mem' := fun a b ha hb => H.hMul_mem hb ha
      inv_mem' := fun a => H.inv_mem }
  left_inv H := SetLike.coe_injective rfl
  right_inv H := SetLike.coe_injective rfl
#align subgroup.opposite Subgroup.opEquiv
#align add_subgroup.opposite AddSubgroup.opEquiv
-/

#print Subgroup.equivOp /-
/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive "Bijection between an additive subgroup `H` and its opposite.", simps]
def equivOp (H : Subgroup G) : H ≃ H.opEquiv :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl
#align subgroup.opposite_equiv Subgroup.equivOp
#align add_subgroup.opposite_equiv AddSubgroup.equivOp
-/

@[to_additive]
instance (H : Subgroup G) [Encodable H] : Encodable H.opEquiv :=
  Encodable.ofEquiv H H.equivOp.symm

@[to_additive]
instance (H : Subgroup G) [Countable H] : Countable H.opEquiv :=
  Countable.of_equiv H H.equivOp

#print Subgroup.smul_opposite_mul /-
@[to_additive]
theorem smul_opposite_mul {H : Subgroup G} (x g : G) (h : H.opEquiv) : h • (g * x) = g * h • x :=
  by
  cases h
  simp [(· • ·), mul_assoc]
#align subgroup.smul_opposite_mul Subgroup.smul_opposite_mul
#align add_subgroup.vadd_opposite_add AddSubgroup.vadd_opposite_add
-/

end Subgroup

