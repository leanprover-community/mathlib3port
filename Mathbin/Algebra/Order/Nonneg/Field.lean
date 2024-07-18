/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Algebra.Order.Field.Basic
import Algebra.Order.Field.Canonical.Defs
import Algebra.Order.Field.InjSurj
import Algebra.Order.Ring.Unbundled.Nonneg

#align_import algebra.order.nonneg.field from "leanprover-community/mathlib"@"b3f4f007a962e3787aa0f3b5c7942a1317f7d88e"

/-!
# Semifield structure on the type of nonnegative elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_semifield` if `α` is a `linear_ordered_field`.
-/


open Set

variable {α : Type _}

namespace Nonneg

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] {x y : α}

#print Nonneg.inv /-
instance inv : Inv { x : α // 0 ≤ x } :=
  ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩
#align nonneg.has_inv Nonneg.inv
-/

#print Nonneg.coe_inv /-
@[simp, norm_cast]
protected theorem coe_inv (a : { x : α // 0 ≤ x }) : ((a⁻¹ : { x : α // 0 ≤ x }) : α) = a⁻¹ :=
  rfl
#align nonneg.coe_inv Nonneg.coe_inv
-/

#print Nonneg.inv_mk /-
@[simp]
theorem inv_mk (hx : 0 ≤ x) : (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ :=
  rfl
#align nonneg.inv_mk Nonneg.inv_mk
-/

#print Nonneg.div /-
instance div : Div { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩
#align nonneg.has_div Nonneg.div
-/

#print Nonneg.coe_div /-
@[simp, norm_cast]
protected theorem coe_div (a b : { x : α // 0 ≤ x }) : ((a / b : { x : α // 0 ≤ x }) : α) = a / b :=
  rfl
#align nonneg.coe_div Nonneg.coe_div
-/

#print Nonneg.mk_div_mk /-
@[simp]
theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl
#align nonneg.mk_div_mk Nonneg.mk_div_mk
-/

#print Nonneg.zpow /-
instance zpow : Pow { x : α // 0 ≤ x } ℤ :=
  ⟨fun a n => ⟨a ^ n, zpow_nonneg a.2 _⟩⟩
#align nonneg.has_zpow Nonneg.zpow
-/

#print Nonneg.coe_zpow /-
@[simp, norm_cast]
protected theorem coe_zpow (a : { x : α // 0 ≤ x }) (n : ℤ) :
    ((a ^ n : { x : α // 0 ≤ x }) : α) = a ^ n :=
  rfl
#align nonneg.coe_zpow Nonneg.coe_zpow
-/

#print Nonneg.mk_zpow /-
@[simp]
theorem mk_zpow (hx : 0 ≤ x) (n : ℤ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ :=
  rfl
#align nonneg.mk_zpow Nonneg.mk_zpow
-/

#print Nonneg.linearOrderedSemifield /-
instance linearOrderedSemifield : LinearOrderedSemifield { x : α // 0 ≤ x } :=
  Subtype.coe_injective.LinearOrderedSemifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) Nonneg.coe_pow Nonneg.coe_zpow
    Nonneg.coe_natCast (fun _ _ => rfl) fun _ _ => rfl
#align nonneg.linear_ordered_semifield Nonneg.linearOrderedSemifield
-/

end LinearOrderedSemifield

#print Nonneg.canonicallyLinearOrderedSemifield /-
instance canonicallyLinearOrderedSemifield [LinearOrderedField α] :
    CanonicallyLinearOrderedSemifield { x : α // 0 ≤ x } :=
  { Nonneg.linearOrderedSemifield, Nonneg.canonicallyOrderedCommSemiring with }
#align nonneg.canonically_linear_ordered_semifield Nonneg.canonicallyLinearOrderedSemifield
-/

#print Nonneg.linearOrderedCommGroupWithZero /-
instance linearOrderedCommGroupWithZero [LinearOrderedField α] :
    LinearOrderedCommGroupWithZero { x : α // 0 ≤ x } :=
  inferInstance
#align nonneg.linear_ordered_comm_group_with_zero Nonneg.linearOrderedCommGroupWithZero
-/

end Nonneg

