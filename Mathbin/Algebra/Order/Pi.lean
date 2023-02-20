/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

! This file was ported from Lean 3 source module algebra.order.pi
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Ring.Defs
import Mathbin.Algebra.Ring.Pi
import Mathbin.Tactic.Positivity

/-!
# Pi instances for ordered groups and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/


universe u v w

variable {ι α β : Type _}

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

#print Pi.orderedCommMonoid /-
/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive
      "The product of a family of ordered additive commutative monoids is\n  an ordered additive commutative monoid."]
instance orderedCommMonoid {ι : Type _} {Z : ι → Type _} [∀ i, OrderedCommMonoid (Z i)] :
    OrderedCommMonoid (∀ i, Z i) :=
  { Pi.partialOrder, Pi.commMonoid with
    mul_le_mul_left := fun f g w h i => mul_le_mul_left' (w i) _ }
#align pi.ordered_comm_monoid Pi.orderedCommMonoid
#align pi.ordered_add_comm_monoid Pi.orderedAddCommMonoid
-/

@[to_additive]
instance {ι : Type _} {α : ι → Type _} [∀ i, LE (α i)] [∀ i, Mul (α i)] [∀ i, ExistsMulOfLE (α i)] :
    ExistsMulOfLE (∀ i, α i) :=
  ⟨fun a b h =>
    ⟨fun i => (exists_mul_of_le <| h i).some,
      funext fun i => (exists_mul_of_le <| h i).choose_spec⟩⟩

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive
      "The product of a family of canonically ordered additive monoids is\n  a canonically ordered additive monoid."]
instance {ι : Type _} {Z : ι → Type _} [∀ i, CanonicallyOrderedMonoid (Z i)] :
    CanonicallyOrderedMonoid (∀ i, Z i) :=
  { Pi.orderBot, Pi.orderedCommMonoid, Pi.existsMulOfLe with
    le_self_mul := fun f g i => le_self_mul }

#print Pi.orderedCancelCommMonoid /-
@[to_additive]
instance orderedCancelCommMonoid [∀ i, OrderedCancelCommMonoid <| f i] :
    OrderedCancelCommMonoid (∀ i : I, f i) := by
  refine_struct
      { Pi.partialOrder, Pi.monoid with
        mul := (· * ·)
        one := (1 : ∀ i, f i)
        le := (· ≤ ·)
        lt := (· < ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.ordered_cancel_comm_monoid Pi.orderedCancelCommMonoid
#align pi.ordered_cancel_add_comm_monoid Pi.orderedAddCancelCommMonoid
-/

#print Pi.orderedCommGroup /-
@[to_additive]
instance orderedCommGroup [∀ i, OrderedCommGroup <| f i] : OrderedCommGroup (∀ i : I, f i) :=
  { Pi.commGroup, Pi.orderedCommMonoid with
    mul := (· * ·)
    one := (1 : ∀ i, f i)
    le := (· ≤ ·)
    lt := (· < ·)
    npow := Monoid.npow }
#align pi.ordered_comm_group Pi.orderedCommGroup
#align pi.ordered_add_comm_group Pi.orderedAddCommGroup
-/

instance [∀ i, OrderedSemiring (f i)] : OrderedSemiring (∀ i, f i) :=
  { Pi.semiring,
    Pi.partialOrder with
    add_le_add_left := fun a b hab c i => add_le_add_left (hab _) _
    zero_le_one := fun _ => zero_le_one
    mul_le_mul_of_nonneg_left := fun a b c hab hc i => mul_le_mul_of_nonneg_left (hab _) <| hc _
    mul_le_mul_of_nonneg_right := fun a b c hab hc i => mul_le_mul_of_nonneg_right (hab _) <| hc _ }

instance [∀ i, OrderedCommSemiring (f i)] : OrderedCommSemiring (∀ i, f i) :=
  { Pi.commSemiring, Pi.orderedSemiring with }

instance [∀ i, OrderedRing (f i)] : OrderedRing (∀ i, f i) :=
  { Pi.ring, Pi.orderedSemiring with mul_nonneg := fun a b ha hb i => mul_nonneg (ha _) (hb _) }

instance [∀ i, OrderedCommRing (f i)] : OrderedCommRing (∀ i, f i) :=
  { Pi.commRing, Pi.orderedRing with }

end Pi

namespace Function

variable (β) [One α] [Preorder α] {a : α}

/- warning: function.one_le_const_of_one_le -> Function.one_le_const_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (β : Type.{u2}) [_inst_1 : One.{u1} α] [_inst_2 : Preorder.{u1} α] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))) a) -> (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u1} α _inst_2)) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (OfNat.mk.{max u2 u1} (β -> α) 1 (One.one.{max u2 u1} (β -> α) (Pi.instOne.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_1))))) (Function.const.{succ u1, succ u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} (β : Type.{u1}) [_inst_1 : One.{u2} α] [_inst_2 : Preorder.{u2} α] {a : α}, (LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1)) a) -> (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u2} α _inst_2)) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (One.toOfNat1.{max u2 u1} (β -> α) (Pi.instOne.{u1, u2} β (fun (a._@.Init.Prelude._hyg.54 : β) => α) (fun (i : β) => _inst_1)))) (Function.const.{succ u2, succ u1} α β a))
Case conversion may be inaccurate. Consider using '#align function.one_le_const_of_one_le Function.one_le_const_of_one_leₓ'. -/
@[to_additive const_nonneg_of_nonneg]
theorem one_le_const_of_one_le (ha : 1 ≤ a) : 1 ≤ const β a := fun _ => ha
#align function.one_le_const_of_one_le Function.one_le_const_of_one_le
#align function.const_nonneg_of_nonneg Function.const_nonneg_of_nonneg

/- warning: function.const_le_one_of_le_one -> Function.const_le_one_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (β : Type.{u2}) [_inst_1 : One.{u1} α] [_inst_2 : Preorder.{u1} α] {a : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1)))) -> (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u1} α _inst_2)) (Function.const.{succ u1, succ u2} α β a) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (OfNat.mk.{max u2 u1} (β -> α) 1 (One.one.{max u2 u1} (β -> α) (Pi.instOne.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} (β : Type.{u1}) [_inst_1 : One.{u2} α] [_inst_2 : Preorder.{u2} α] {a : α}, (LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) a (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1))) -> (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u2} α _inst_2)) (Function.const.{succ u2, succ u1} α β a) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (One.toOfNat1.{max u2 u1} (β -> α) (Pi.instOne.{u1, u2} β (fun (a._@.Init.Prelude._hyg.54 : β) => α) (fun (i : β) => _inst_1)))))
Case conversion may be inaccurate. Consider using '#align function.const_le_one_of_le_one Function.const_le_one_of_le_oneₓ'. -/
@[to_additive]
theorem const_le_one_of_le_one (ha : a ≤ 1) : const β a ≤ 1 := fun _ => ha
#align function.const_le_one_of_le_one Function.const_le_one_of_le_one
#align function.const_nonpos_of_nonpos Function.const_nonpos_of_nonpos

variable {β} [Nonempty β]

/- warning: function.one_le_const -> Function.one_le_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : One.{u1} α] [_inst_2 : Preorder.{u1} α] {a : α} [_inst_3 : Nonempty.{succ u2} β], Iff (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u1} α _inst_2)) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (OfNat.mk.{max u2 u1} (β -> α) 1 (One.one.{max u2 u1} (β -> α) (Pi.instOne.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_1))))) (Function.const.{succ u1, succ u2} α β a)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : One.{u2} α] [_inst_2 : Preorder.{u2} α] {a : α} [_inst_3 : Nonempty.{succ u1} β], Iff (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u2} α _inst_2)) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (One.toOfNat1.{max u2 u1} (β -> α) (Pi.instOne.{u1, u2} β (fun (a._@.Init.Prelude._hyg.54 : β) => α) (fun (i : β) => _inst_1)))) (Function.const.{succ u2, succ u1} α β a)) (LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align function.one_le_const Function.one_le_constₓ'. -/
@[simp, to_additive const_nonneg]
theorem one_le_const : 1 ≤ const β a ↔ 1 ≤ a :=
  @const_le_const _ _ _ _ 1 _
#align function.one_le_const Function.one_le_const
#align function.const_nonneg Function.const_nonneg

/- warning: function.one_lt_const -> Function.one_lt_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : One.{u1} α] [_inst_2 : Preorder.{u1} α] {a : α} [_inst_3 : Nonempty.{succ u2} β], Iff (LT.lt.{max u2 u1} (β -> α) (Preorder.toLT.{max u2 u1} (β -> α) (Pi.preorder.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_2))) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (OfNat.mk.{max u2 u1} (β -> α) 1 (One.one.{max u2 u1} (β -> α) (Pi.instOne.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_1))))) (Function.const.{succ u1, succ u2} α β a)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : One.{u2} α] [_inst_2 : Preorder.{u2} α] {a : α} [_inst_3 : Nonempty.{succ u1} β], Iff (LT.lt.{max u2 u1} (β -> α) (Preorder.toLT.{max u2 u1} (β -> α) (Pi.preorder.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_2))) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (One.toOfNat1.{max u2 u1} (β -> α) (Pi.instOne.{u1, u2} β (fun (a._@.Init.Prelude._hyg.54 : β) => α) (fun (i : β) => _inst_1)))) (Function.const.{succ u2, succ u1} α β a)) (LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align function.one_lt_const Function.one_lt_constₓ'. -/
@[simp, to_additive const_pos]
theorem one_lt_const : 1 < const β a ↔ 1 < a :=
  @const_lt_const _ _ _ _ 1 a
#align function.one_lt_const Function.one_lt_const
#align function.const_pos Function.const_pos

/- warning: function.const_le_one -> Function.const_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : One.{u1} α] [_inst_2 : Preorder.{u1} α] {a : α} [_inst_3 : Nonempty.{succ u2} β], Iff (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u1} α _inst_2)) (Function.const.{succ u1, succ u2} α β a) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (OfNat.mk.{max u2 u1} (β -> α) 1 (One.one.{max u2 u1} (β -> α) (Pi.instOne.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : One.{u2} α] [_inst_2 : Preorder.{u2} α] {a : α} [_inst_3 : Nonempty.{succ u1} β], Iff (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u2} α _inst_2)) (Function.const.{succ u2, succ u1} α β a) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (One.toOfNat1.{max u2 u1} (β -> α) (Pi.instOne.{u1, u2} β (fun (a._@.Init.Prelude._hyg.54 : β) => α) (fun (i : β) => _inst_1))))) (LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) a (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align function.const_le_one Function.const_le_oneₓ'. -/
@[simp, to_additive]
theorem const_le_one : const β a ≤ 1 ↔ a ≤ 1 :=
  @const_le_const _ _ _ _ _ 1
#align function.const_le_one Function.const_le_one
#align function.const_nonpos Function.const_nonpos

/- warning: function.const_lt_one -> Function.const_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : One.{u1} α] [_inst_2 : Preorder.{u1} α] {a : α} [_inst_3 : Nonempty.{succ u2} β], Iff (LT.lt.{max u2 u1} (β -> α) (Preorder.toLT.{max u2 u1} (β -> α) (Pi.preorder.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_2))) (Function.const.{succ u1, succ u2} α β a) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (OfNat.mk.{max u2 u1} (β -> α) 1 (One.one.{max u2 u1} (β -> α) (Pi.instOne.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_1)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : One.{u2} α] [_inst_2 : Preorder.{u2} α] {a : α} [_inst_3 : Nonempty.{succ u1} β], Iff (LT.lt.{max u2 u1} (β -> α) (Preorder.toLT.{max u2 u1} (β -> α) (Pi.preorder.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => _inst_2))) (Function.const.{succ u2, succ u1} α β a) (OfNat.ofNat.{max u2 u1} (β -> α) 1 (One.toOfNat1.{max u2 u1} (β -> α) (Pi.instOne.{u1, u2} β (fun (a._@.Init.Prelude._hyg.54 : β) => α) (fun (i : β) => _inst_1))))) (LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) a (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align function.const_lt_one Function.const_lt_oneₓ'. -/
@[simp, to_additive]
theorem const_lt_one : const β a < 1 ↔ a < 1 :=
  @const_lt_const _ _ _ _ _ 1
#align function.const_lt_one Function.const_lt_one
#align function.const_neg Function.const_neg

end Function

namespace Tactic

open Function Positivity

variable (ι) [Zero α] {a : α}

private theorem function_const_nonneg_of_pos [Preorder α] (ha : 0 < a) : 0 ≤ const ι a :=
  const_nonneg_of_nonneg _ ha.le
#align tactic.function_const_nonneg_of_pos tactic.function_const_nonneg_of_pos

variable [Nonempty ι]

private theorem function_const_ne_zero : a ≠ 0 → const ι a ≠ 0 :=
  const_ne_zero.2
#align tactic.function_const_ne_zero tactic.function_const_ne_zero

private theorem function_const_pos [Preorder α] : 0 < a → 0 < const ι a :=
  const_pos.2
#align tactic.function_const_pos tactic.function_const_pos

/-- Extension for the `positivity` tactic: `function.const` is positive/nonnegative/nonzero if its
input is. -/
@[positivity]
unsafe def positivity_const : expr → tactic strictness
  | q(Function.const $(ι) $(a)) => do
    let strict_a ← core a
    match strict_a with
      | positive p =>
        positive <$> to_expr ``(function_const_pos $(ι) $(p)) <|>
          nonnegative <$> to_expr ``(function_const_nonneg_of_pos $(ι) $(p))
      | nonnegative p => nonnegative <$> to_expr ``(const_nonneg_of_nonneg $(ι) $(p))
      | nonzero p => nonzero <$> to_expr ``(function_const_ne_zero $(ι) $(p))
  | e =>
    pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `function.const ι a`"
#align tactic.positivity_const tactic.positivity_const

end Tactic

