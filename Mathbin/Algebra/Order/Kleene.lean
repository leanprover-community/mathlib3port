/-
Copyright (c) 2022 Siddhartha Prasad, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Prasad, Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.kleene
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Ring.Canonical
import Mathbin.Algebra.Ring.Pi
import Mathbin.Algebra.Ring.Prod
import Mathbin.Order.Hom.CompleteLattice

/-!
# Kleene Algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines idempotent semirings and Kleene algebras, which are used extensively in the theory
of computation.

An idempotent semiring is a semiring whose addition is idempotent. An idempotent semiring is
naturally a semilattice by setting `a ≤ b` if `a + b = b`.

A Kleene algebra is an idempotent semiring equipped with an additional unary operator `∗`, the
Kleene star.

## Main declarations

* `idem_semiring`: Idempotent semiring
* `idem_comm_semiring`: Idempotent commutative semiring
* `kleene_algebra`: Kleene algebra

## Notation

`a∗` is notation for `kstar a` in locale `computability`.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*]
  [kozen1994]
* https://planetmath.org/idempotentsemiring
* https://encyclopediaofmath.org/wiki/Idempotent_semi-ring
* https://planetmath.org/kleene_algebra

## TODO

Instances for `add_opposite`, `mul_opposite`, `ulift`, `subsemiring`, `subring`, `subalgebra`.

## Tags

kleene algebra, idempotent semiring
-/


open Function

universe u

variable {α β ι : Type _} {π : ι → Type _}

#print IdemSemiring /-
/-- An idempotent semiring is a semiring with the additional property that addition is idempotent.
-/
@[protect_proj]
class IdemSemiring (α : Type u) extends Semiring α, SemilatticeSup α where
  sup := (· + ·)
  add_eq_sup : ∀ a b : α, a + b = a ⊔ b := by
    intros
    rfl
  bot : α := 0
  bot_le : ∀ a, bot ≤ a
#align idem_semiring IdemSemiring
-/

#print IdemCommSemiring /-
/-- An idempotent commutative semiring is a commutative semiring with the additional property that
addition is idempotent. -/
@[protect_proj]
class IdemCommSemiring (α : Type u) extends CommSemiring α, IdemSemiring α
#align idem_comm_semiring IdemCommSemiring
-/

#print KStar /-
/-- Notation typeclass for the Kleene star `∗`. -/
@[protect_proj]
class KStar (α : Type _) where
  kstar : α → α
#align has_kstar KStar
-/

-- mathport name: «expr ∗»
scoped[Computability] postfix:1024 "∗" => KStar.kstar

#print KleeneAlgebra /-
/-- A Kleene Algebra is an idempotent semiring with an additional unary operator `kstar` (for Kleene
star) that satisfies the following properties:
* `1 + a * a∗ ≤ a∗`
* `1 + a∗ * a ≤ a∗`
* If `a * c + b ≤ c`, then `a∗ * b ≤ c`
* If `c * a + b ≤ c`, then `b * a∗ ≤ c`
-/
@[protect_proj]
class KleeneAlgebra (α : Type _) extends IdemSemiring α, KStar α where
  one_le_kstar : ∀ a : α, 1 ≤ a∗
  mul_kstar_le_kstar : ∀ a : α, a * a∗ ≤ a∗
  kstar_mul_le_kstar : ∀ a : α, a∗ * a ≤ a∗
  mul_kstar_le_self : ∀ a b : α, b * a ≤ b → b * a∗ ≤ b
  kstar_mul_le_self : ∀ a b : α, a * b ≤ b → a∗ * b ≤ b
#align kleene_algebra KleeneAlgebra
-/

#print IdemSemiring.toOrderBot /-
-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toOrderBot [IdemSemiring α] : OrderBot α :=
  { ‹IdemSemiring α› with }
#align idem_semiring.to_order_bot IdemSemiring.toOrderBot
-/

/- warning: idem_semiring.of_semiring -> IdemSemiring.ofSemiring is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], (forall (a : α), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a a) a) -> (IdemSemiring.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], (forall (a : α), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a a) a) -> (IdemSemiring.{u1} α)
Case conversion may be inaccurate. Consider using '#align idem_semiring.of_semiring IdemSemiring.ofSemiringₓ'. -/
-- See note [reducible non-instances]
/-- Construct an idempotent semiring from an idempotent addition. -/
@[reducible]
def IdemSemiring.ofSemiring [Semiring α] (h : ∀ a : α, a + a = a) : IdemSemiring α :=
  { ‹Semiring α› with
    le := fun a b => a + b = b
    le_refl := h
    le_trans := fun a b c (hab : _ = _) (hbc : _ = _) =>
      by
      change _ = _
      rw [← hbc, ← add_assoc, hab]
    le_antisymm := fun a b (hab : _ = _) (hba : _ = _) => by rwa [← hba, add_comm]
    sup := (· + ·)
    le_sup_left := fun a b => by
      change _ = _
      rw [← add_assoc, h]
    le_sup_right := fun a b => by
      change _ = _
      rw [add_comm, add_assoc, h]
    sup_le := fun a b c hab (hbc : _ = _) => by
      change _ = _
      rwa [add_assoc, hbc]
    bot := 0
    bot_le := zero_add }
#align idem_semiring.of_semiring IdemSemiring.ofSemiring

section IdemSemiring

variable [IdemSemiring α] {a b c : α}

/- warning: add_eq_sup -> add_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align add_eq_sup add_eq_supₓ'. -/
@[simp]
theorem add_eq_sup (a b : α) : a + b = a ⊔ b :=
  IdemSemiring.add_eq_sup _ _
#align add_eq_sup add_eq_sup

/- warning: add_idem -> add_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] (a : α), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] (a : α), Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a a) a
Case conversion may be inaccurate. Consider using '#align add_idem add_idemₓ'. -/
theorem add_idem (a : α) : a + a = a := by simp
#align add_idem add_idem

#print nsmul_eq_self /-
theorem nsmul_eq_self : ∀ {n : ℕ} (hn : n ≠ 0) (a : α), n • a = a
  | 0, h => (h rfl).elim
  | 1, h => one_nsmul
  | n + 2, h => fun a => by rw [succ_nsmul, nsmul_eq_self n.succ_ne_zero, add_idem]
#align nsmul_eq_self nsmul_eq_self
-/

/- warning: add_eq_left_iff_le -> add_eq_left_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) a) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) a) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) b a)
Case conversion may be inaccurate. Consider using '#align add_eq_left_iff_le add_eq_left_iff_leₓ'. -/
theorem add_eq_left_iff_le : a + b = a ↔ b ≤ a := by simp
#align add_eq_left_iff_le add_eq_left_iff_le

/- warning: add_eq_right_iff_le -> add_eq_right_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) b) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align add_eq_right_iff_le add_eq_right_iff_leₓ'. -/
theorem add_eq_right_iff_le : a + b = b ↔ a ≤ b := by simp
#align add_eq_right_iff_le add_eq_right_iff_le

/- warning: has_le.le.add_eq_left -> LE.le.add_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) b a) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) b a) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) a)
Case conversion may be inaccurate. Consider using '#align has_le.le.add_eq_left LE.le.add_eq_leftₓ'. -/
alias add_eq_left_iff_le ↔ _ LE.le.add_eq_left
#align has_le.le.add_eq_left LE.le.add_eq_left

/- warning: has_le.le.add_eq_right -> LE.le.add_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) a b) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) a b) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) b)
Case conversion may be inaccurate. Consider using '#align has_le.le.add_eq_right LE.le.add_eq_rightₓ'. -/
alias add_eq_right_iff_le ↔ _ LE.le.add_eq_right
#align has_le.le.add_eq_right LE.le.add_eq_right

/- warning: add_le_iff -> add_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) c) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) a c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) c) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) a c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align add_le_iff add_le_iffₓ'. -/
theorem add_le_iff : a + b ≤ c ↔ a ≤ c ∧ b ≤ c := by simp
#align add_le_iff add_le_iff

/- warning: add_le -> add_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align add_le add_leₓ'. -/
theorem add_le (ha : a ≤ c) (hb : b ≤ c) : a + b ≤ c :=
  add_le_iff.2 ⟨ha, hb⟩
#align add_le add_le

#print IdemSemiring.toCanonicallyOrderedAddMonoid /-
-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toCanonicallyOrderedAddMonoid :
    CanonicallyOrderedAddMonoid α :=
  {
    ‹IdemSemiring
        α› with
    add_le_add_left := fun a b hbc c => by
      simp_rw [add_eq_sup]
      exact sup_le_sup_left hbc _
    exists_add_of_le := fun a b h => ⟨b, h.add_eq_right.symm⟩
    le_self_add := fun a b => add_eq_right_iff_le.1 <| by rw [← add_assoc, add_idem] }
#align idem_semiring.to_canonically_ordered_add_monoid IdemSemiring.toCanonicallyOrderedAddMonoid
-/

/- warning: idem_semiring.to_covariant_class_mul_le -> IdemSemiring.toCovariantClass_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α], CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α], CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Kleene._hyg.1691 : α) (x._@.Mathlib.Algebra.Order.Kleene._hyg.1693 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Kleene._hyg.1691 x._@.Mathlib.Algebra.Order.Kleene._hyg.1693) (fun (x._@.Mathlib.Algebra.Order.Kleene._hyg.1706 : α) (x._@.Mathlib.Algebra.Order.Kleene._hyg.1708 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Kleene._hyg.1706 x._@.Mathlib.Algebra.Order.Kleene._hyg.1708)
Case conversion may be inaccurate. Consider using '#align idem_semiring.to_covariant_class_mul_le IdemSemiring.toCovariantClass_mul_leₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toCovariantClass_mul_le :
    CovariantClass α α (· * ·) (· ≤ ·) :=
  ⟨fun a b c hbc => add_eq_left_iff_le.1 <| by rw [← mul_add, hbc.add_eq_left]⟩
#align idem_semiring.to_covariant_class_mul_le IdemSemiring.toCovariantClass_mul_le

/- warning: idem_semiring.to_covariant_class_swap_mul_le -> IdemSemiring.toCovariantClass_swap_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α], CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : IdemSemiring.{u1} α], CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Kleene._hyg.1786 : α) (x._@.Mathlib.Algebra.Order.Kleene._hyg.1788 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Kleene._hyg.1786 x._@.Mathlib.Algebra.Order.Kleene._hyg.1788)) (fun (x._@.Mathlib.Algebra.Order.Kleene._hyg.1801 : α) (x._@.Mathlib.Algebra.Order.Kleene._hyg.1803 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Order.Kleene._hyg.1801 x._@.Mathlib.Algebra.Order.Kleene._hyg.1803)
Case conversion may be inaccurate. Consider using '#align idem_semiring.to_covariant_class_swap_mul_le IdemSemiring.toCovariantClass_swap_mul_leₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toCovariantClass_swap_mul_le :
    CovariantClass α α (swap (· * ·)) (· ≤ ·) :=
  ⟨fun a b c hbc => add_eq_left_iff_le.1 <| by rw [← add_mul, hbc.add_eq_left]⟩
#align idem_semiring.to_covariant_class_swap_mul_le IdemSemiring.toCovariantClass_swap_mul_le

end IdemSemiring

section KleeneAlgebra

variable [KleeneAlgebra α] {a b c : α}

/- warning: one_le_kstar -> one_le_kstar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))))) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align one_le_kstar one_le_kstarₓ'. -/
@[simp]
theorem one_le_kstar : 1 ≤ a∗ :=
  KleeneAlgebra.one_le_kstar _
#align one_le_kstar one_le_kstar

/- warning: mul_kstar_le_kstar -> mul_kstar_le_kstar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) a (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align mul_kstar_le_kstar mul_kstar_le_kstarₓ'. -/
theorem mul_kstar_le_kstar : a * a∗ ≤ a∗ :=
  KleeneAlgebra.mul_kstar_le_kstar _
#align mul_kstar_le_kstar mul_kstar_le_kstar

/- warning: kstar_mul_le_kstar -> kstar_mul_le_kstar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a) a) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a) a) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align kstar_mul_le_kstar kstar_mul_le_kstarₓ'. -/
theorem kstar_mul_le_kstar : a∗ * a ≤ a∗ :=
  KleeneAlgebra.kstar_mul_le_kstar _
#align kstar_mul_le_kstar kstar_mul_le_kstar

/- warning: mul_kstar_le_self -> mul_kstar_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) b a) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) b (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) b a) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) b (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)) b)
Case conversion may be inaccurate. Consider using '#align mul_kstar_le_self mul_kstar_le_selfₓ'. -/
theorem mul_kstar_le_self : b * a ≤ b → b * a∗ ≤ b :=
  KleeneAlgebra.mul_kstar_le_self _ _
#align mul_kstar_le_self mul_kstar_le_self

/- warning: kstar_mul_le_self -> kstar_mul_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) a b) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a) b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a b) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a) b) b)
Case conversion may be inaccurate. Consider using '#align kstar_mul_le_self kstar_mul_le_selfₓ'. -/
theorem kstar_mul_le_self : a * b ≤ b → a∗ * b ≤ b :=
  KleeneAlgebra.kstar_mul_le_self _ _
#align kstar_mul_le_self kstar_mul_le_self

/- warning: mul_kstar_le -> mul_kstar_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) c a) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) b (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) c a) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) b (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)) c)
Case conversion may be inaccurate. Consider using '#align mul_kstar_le mul_kstar_leₓ'. -/
theorem mul_kstar_le (hb : b ≤ c) (ha : c * a ≤ c) : b * a∗ ≤ c :=
  (mul_le_mul_right' hb _).trans <| mul_kstar_le_self ha
#align mul_kstar_le mul_kstar_le

/- warning: kstar_mul_le -> kstar_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) a c) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a) b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a c) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a) b) c)
Case conversion may be inaccurate. Consider using '#align kstar_mul_le kstar_mul_leₓ'. -/
theorem kstar_mul_le (hb : b ≤ c) (ha : a * c ≤ c) : a∗ * b ≤ c :=
  (mul_le_mul_left' hb _).trans <| kstar_mul_le_self ha
#align kstar_mul_le kstar_mul_le

/- warning: kstar_le_of_mul_le_left -> kstar_le_of_mul_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) b a) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) b a) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a) b)
Case conversion may be inaccurate. Consider using '#align kstar_le_of_mul_le_left kstar_le_of_mul_le_leftₓ'. -/
theorem kstar_le_of_mul_le_left (hb : 1 ≤ b) : b * a ≤ b → a∗ ≤ b := by simpa using mul_kstar_le hb
#align kstar_le_of_mul_le_left kstar_le_of_mul_le_left

/- warning: kstar_le_of_mul_le_right -> kstar_le_of_mul_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) a b) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a b) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a) b)
Case conversion may be inaccurate. Consider using '#align kstar_le_of_mul_le_right kstar_le_of_mul_le_rightₓ'. -/
theorem kstar_le_of_mul_le_right (hb : 1 ≤ b) : a * b ≤ b → a∗ ≤ b := by simpa using kstar_mul_le hb
#align kstar_le_of_mul_le_right kstar_le_of_mul_le_right

/- warning: le_kstar -> le_kstar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align le_kstar le_kstarₓ'. -/
@[simp]
theorem le_kstar : a ≤ a∗ :=
  le_trans (le_mul_of_one_le_left' one_le_kstar) kstar_mul_le_kstar
#align le_kstar le_kstar

/- warning: kstar_mono -> kstar_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α], Monotone.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α], Monotone.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align kstar_mono kstar_monoₓ'. -/
@[mono]
theorem kstar_mono : Monotone (KStar.kstar : α → α) := fun a b h =>
  kstar_le_of_mul_le_left one_le_kstar <| kstar_mul_le (h.trans le_kstar) <| mul_kstar_le_kstar
#align kstar_mono kstar_mono

/- warning: kstar_eq_one -> kstar_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, Iff (Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, Iff (Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align kstar_eq_one kstar_eq_oneₓ'. -/
@[simp]
theorem kstar_eq_one : a∗ = 1 ↔ a ≤ 1 :=
  ⟨le_kstar.trans_eq, fun h =>
    one_le_kstar.antisymm' <| kstar_le_of_mul_le_left le_rfl <| by rwa [one_mul]⟩
#align kstar_eq_one kstar_eq_one

/- warning: kstar_zero -> kstar_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α], Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α], Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align kstar_zero kstar_zeroₓ'. -/
@[simp]
theorem kstar_zero : (0 : α)∗ = 1 :=
  kstar_eq_one.2 zero_le_one
#align kstar_zero kstar_zero

/- warning: kstar_one -> kstar_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α], Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α], Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align kstar_one kstar_oneₓ'. -/
@[simp]
theorem kstar_one : (1 : α)∗ = 1 :=
  kstar_eq_one.2 le_rfl
#align kstar_one kstar_one

/- warning: kstar_mul_kstar -> kstar_mul_kstar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align kstar_mul_kstar kstar_mul_kstarₓ'. -/
@[simp]
theorem kstar_mul_kstar (a : α) : a∗ * a∗ = a∗ :=
  (mul_kstar_le le_rfl <| kstar_mul_le_kstar).antisymm <| le_mul_of_one_le_left' one_le_kstar
#align kstar_mul_kstar kstar_mul_kstar

/- warning: kstar_eq_self -> kstar_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, Iff (Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a) a) (And (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) a a) a) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α}, Iff (Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a) a) (And (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a a) a) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) a))
Case conversion may be inaccurate. Consider using '#align kstar_eq_self kstar_eq_selfₓ'. -/
@[simp]
theorem kstar_eq_self : a∗ = a ↔ a * a = a ∧ 1 ≤ a :=
  ⟨fun h => ⟨by rw [← h, kstar_mul_kstar], one_le_kstar.trans_eq h⟩, fun h =>
    (kstar_le_of_mul_le_left h.2 h.1.le).antisymm le_kstar⟩
#align kstar_eq_self kstar_eq_self

/- warning: kstar_idem -> kstar_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] (a : α), Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] (a : α), Eq.{succ u1} α (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align kstar_idem kstar_idemₓ'. -/
@[simp]
theorem kstar_idem (a : α) : a∗∗ = a∗ :=
  kstar_eq_self.2 ⟨kstar_mul_kstar _, one_le_kstar⟩
#align kstar_idem kstar_idem

/- warning: pow_le_kstar -> pow_le_kstar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {n : Nat}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a n) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : KleeneAlgebra.{u1} α] {a : α} {n : Nat}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) a n) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align pow_le_kstar pow_le_kstarₓ'. -/
@[simp]
theorem pow_le_kstar : ∀ {n : ℕ}, a ^ n ≤ a∗
  | 0 => (pow_zero _).trans_le one_le_kstar
  | n + 1 => by
    rw [pow_succ]
    exact (mul_le_mul_left' pow_le_kstar _).trans mul_kstar_le_kstar
#align pow_le_kstar pow_le_kstar

end KleeneAlgebra

namespace Prod

instance [IdemSemiring α] [IdemSemiring β] : IdemSemiring (α × β) :=
  { Prod.semiring, Prod.semilatticeSup _ _, Prod.orderBot _ _ with
    add_eq_sup := fun a b => ext (add_eq_sup _ _) (add_eq_sup _ _) }

instance [IdemCommSemiring α] [IdemCommSemiring β] : IdemCommSemiring (α × β) :=
  { Prod.commSemiring, Prod.idemSemiring with }

variable [KleeneAlgebra α] [KleeneAlgebra β]

instance : KleeneAlgebra (α × β) :=
  { Prod.idemSemiring with
    kstar := fun a => (a.1∗, a.2∗)
    one_le_kstar := fun a => ⟨one_le_kstar, one_le_kstar⟩
    mul_kstar_le_kstar := fun a => ⟨mul_kstar_le_kstar, mul_kstar_le_kstar⟩
    kstar_mul_le_kstar := fun a => ⟨kstar_mul_le_kstar, kstar_mul_le_kstar⟩
    mul_kstar_le_self := fun a b => And.imp mul_kstar_le_self mul_kstar_le_self
    kstar_mul_le_self := fun a b => And.imp kstar_mul_le_self kstar_mul_le_self }

/- warning: prod.kstar_def -> Prod.kstar_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : KleeneAlgebra.{u1} α] [_inst_2 : KleeneAlgebra.{u2} β] (a : Prod.{u1, u2} α β), Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (KStar.kstar.{max u1 u2} (Prod.{u1, u2} α β) (KleeneAlgebra.toHasKstar.{max u1 u2} (Prod.{u1, u2} α β) (Prod.kleeneAlgebra.{u1, u2} α β _inst_1 _inst_2)) a) (Prod.mk.{u1, u2} α β (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) (Prod.fst.{u1, u2} α β a)) (KStar.kstar.{u2} β (KleeneAlgebra.toHasKstar.{u2} β _inst_2) (Prod.snd.{u1, u2} α β a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : KleeneAlgebra.{u2} α] [_inst_2 : KleeneAlgebra.{u1} β] (a : Prod.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (KStar.kstar.{max u2 u1} (Prod.{u2, u1} α β) (KleeneAlgebra.toKStar.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instKleeneAlgebraProd.{u2, u1} α β _inst_1 _inst_2)) a) (Prod.mk.{u2, u1} α β (KStar.kstar.{u2} α (KleeneAlgebra.toKStar.{u2} α _inst_1) (Prod.fst.{u2, u1} α β a)) (KStar.kstar.{u1} β (KleeneAlgebra.toKStar.{u1} β _inst_2) (Prod.snd.{u2, u1} α β a)))
Case conversion may be inaccurate. Consider using '#align prod.kstar_def Prod.kstar_defₓ'. -/
theorem kstar_def (a : α × β) : a∗ = (a.1∗, a.2∗) :=
  rfl
#align prod.kstar_def Prod.kstar_def

/- warning: prod.fst_kstar -> Prod.fst_kstar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : KleeneAlgebra.{u1} α] [_inst_2 : KleeneAlgebra.{u2} β] (a : Prod.{u1, u2} α β), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (KStar.kstar.{max u1 u2} (Prod.{u1, u2} α β) (KleeneAlgebra.toHasKstar.{max u1 u2} (Prod.{u1, u2} α β) (Prod.kleeneAlgebra.{u1, u2} α β _inst_1 _inst_2)) a)) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) (Prod.fst.{u1, u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : KleeneAlgebra.{u2} α] [_inst_2 : KleeneAlgebra.{u1} β] (a : Prod.{u2, u1} α β), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (KStar.kstar.{max u2 u1} (Prod.{u2, u1} α β) (KleeneAlgebra.toKStar.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instKleeneAlgebraProd.{u2, u1} α β _inst_1 _inst_2)) a)) (KStar.kstar.{u2} α (KleeneAlgebra.toKStar.{u2} α _inst_1) (Prod.fst.{u2, u1} α β a))
Case conversion may be inaccurate. Consider using '#align prod.fst_kstar Prod.fst_kstarₓ'. -/
@[simp]
theorem fst_kstar (a : α × β) : a∗.1 = a.1∗ :=
  rfl
#align prod.fst_kstar Prod.fst_kstar

/- warning: prod.snd_kstar -> Prod.snd_kstar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : KleeneAlgebra.{u1} α] [_inst_2 : KleeneAlgebra.{u2} β] (a : Prod.{u1, u2} α β), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (KStar.kstar.{max u1 u2} (Prod.{u1, u2} α β) (KleeneAlgebra.toHasKstar.{max u1 u2} (Prod.{u1, u2} α β) (Prod.kleeneAlgebra.{u1, u2} α β _inst_1 _inst_2)) a)) (KStar.kstar.{u2} β (KleeneAlgebra.toHasKstar.{u2} β _inst_2) (Prod.snd.{u1, u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : KleeneAlgebra.{u2} α] [_inst_2 : KleeneAlgebra.{u1} β] (a : Prod.{u2, u1} α β), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (KStar.kstar.{max u2 u1} (Prod.{u2, u1} α β) (KleeneAlgebra.toKStar.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instKleeneAlgebraProd.{u2, u1} α β _inst_1 _inst_2)) a)) (KStar.kstar.{u1} β (KleeneAlgebra.toKStar.{u1} β _inst_2) (Prod.snd.{u2, u1} α β a))
Case conversion may be inaccurate. Consider using '#align prod.snd_kstar Prod.snd_kstarₓ'. -/
@[simp]
theorem snd_kstar (a : α × β) : a∗.2 = a.2∗ :=
  rfl
#align prod.snd_kstar Prod.snd_kstar

end Prod

namespace Pi

instance [∀ i, IdemSemiring (π i)] : IdemSemiring (∀ i, π i) :=
  { Pi.semiring, Pi.semilatticeSup, Pi.orderBot with
    add_eq_sup := fun a b => funext fun i => add_eq_sup _ _ }

instance [∀ i, IdemCommSemiring (π i)] : IdemCommSemiring (∀ i, π i) :=
  { Pi.commSemiring, Pi.idemSemiring with }

variable [∀ i, KleeneAlgebra (π i)]

instance : KleeneAlgebra (∀ i, π i) :=
  { Pi.idemSemiring with
    kstar := fun a i => (a i)∗
    one_le_kstar := fun a i => one_le_kstar
    mul_kstar_le_kstar := fun a i => mul_kstar_le_kstar
    kstar_mul_le_kstar := fun a i => kstar_mul_le_kstar
    mul_kstar_le_self := fun a b h i => mul_kstar_le_self <| h _
    kstar_mul_le_self := fun a b h i => kstar_mul_le_self <| h _ }

/- warning: pi.kstar_def -> Pi.kstar_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), KleeneAlgebra.{u2} (π i)] (a : forall (i : ι), π i), Eq.{succ (max u1 u2)} (forall (i : ι), π i) (KStar.kstar.{max u1 u2} (forall (i : ι), π i) (KleeneAlgebra.toHasKstar.{max u1 u2} (forall (i : ι), π i) (Pi.kleeneAlgebra.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => _inst_1 i))) a) (fun (i : ι) => KStar.kstar.{u2} (π i) (KleeneAlgebra.toHasKstar.{u2} (π i) (_inst_1 i)) (a i))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : forall (i : ι), KleeneAlgebra.{u1} (π i)] (a : forall (i : ι), π i), Eq.{max (succ u2) (succ u1)} (forall (i : ι), π i) (KStar.kstar.{max u2 u1} (forall (i : ι), π i) (KleeneAlgebra.toKStar.{max u2 u1} (forall (i : ι), π i) (Pi.instKleeneAlgebraForAll.{u2, u1} ι (fun (i : ι) => π i) (fun (i : ι) => _inst_1 i))) a) (fun (i : ι) => KStar.kstar.{u1} (π i) (KleeneAlgebra.toKStar.{u1} (π i) (_inst_1 i)) (a i))
Case conversion may be inaccurate. Consider using '#align pi.kstar_def Pi.kstar_defₓ'. -/
theorem kstar_def (a : ∀ i, π i) : a∗ = fun i => (a i)∗ :=
  rfl
#align pi.kstar_def Pi.kstar_def

/- warning: pi.kstar_apply -> Pi.kstar_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), KleeneAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (i : ι), Eq.{succ u2} (π i) (KStar.kstar.{max u1 u2} (forall (i : ι), π i) (KleeneAlgebra.toHasKstar.{max u1 u2} (forall (i : ι), π i) (Pi.kleeneAlgebra.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => _inst_1 i))) a i) (KStar.kstar.{u2} (π i) (KleeneAlgebra.toHasKstar.{u2} (π i) (_inst_1 i)) (a i))
but is expected to have type
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), KleeneAlgebra.{u2} (π i)] (a : forall (i : ι), π i) (i : ι), Eq.{succ u2} (π i) (KStar.kstar.{max u1 u2} (forall (i : ι), π i) (KleeneAlgebra.toKStar.{max u1 u2} (forall (i : ι), π i) (Pi.instKleeneAlgebraForAll.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => _inst_1 i))) a i) (KStar.kstar.{u2} (π i) (KleeneAlgebra.toKStar.{u2} (π i) (_inst_1 i)) (a i))
Case conversion may be inaccurate. Consider using '#align pi.kstar_apply Pi.kstar_applyₓ'. -/
@[simp]
theorem kstar_apply (a : ∀ i, π i) (i : ι) : a∗ i = (a i)∗ :=
  rfl
#align pi.kstar_apply Pi.kstar_apply

end Pi

namespace Function.Injective

/- warning: function.injective.idem_semiring -> Function.Injective.idemSemiring is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : IdemSemiring.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : One.{u2} β] [_inst_4 : Add.{u2} β] [_inst_5 : Mul.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : SMul.{0, u2} Nat β] [_inst_8 : NatCast.{u2} β] [_inst_9 : HasSup.{u2} β] [_inst_10 : Bot.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))))))) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_3)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_4) x y)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_5) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (SMul.smul.{0, u2} Nat β _inst_7 n x)) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) n (f x))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))) (f x) n)) -> (forall (n : Nat), Eq.{succ u1} α (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u2} Nat β (CoeTCₓ.coe.{1, succ u2} Nat β (Nat.castCoe.{u2} β _inst_8))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))))) n)) -> (forall (a : β) (b : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_9 a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)) (f a) (f b))) -> (Eq.{succ u1} α (f (Bot.bot.{u2} β _inst_10)) (Bot.bot.{u1} α (CanonicallyOrderedAddMonoid.toHasBot.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))) -> (IdemSemiring.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : IdemSemiring.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : One.{u2} β] [_inst_4 : Add.{u2} β] [_inst_5 : Mul.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : SMul.{0, u2} Nat β] [_inst_8 : NatCast.{u2} β] [_inst_9 : HasSup.{u2} β] [_inst_10 : Bot.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_3))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_4) x y)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)))))) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_5) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HSMul.hSMul.{0, u2, u2} Nat β β (instHSMul.{0, u2} Nat β _inst_7) n x)) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))))) n (f x))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1))))) (f x) n)) -> (forall (n : Nat), Eq.{succ u1} α (f (Nat.cast.{u2} β _inst_8 n)) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (IdemSemiring.toSemiring.{u1} α _inst_1)) n)) -> (forall (a : β) (b : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_9 a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α _inst_1)) (f a) (f b))) -> (Eq.{succ u1} α (f (Bot.bot.{u2} β _inst_10)) (Bot.bot.{u1} α (CanonicallyOrderedAddMonoid.toBot.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α _inst_1)))) -> (IdemSemiring.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.idem_semiring Function.Injective.idemSemiringₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `idem_semiring` instance along an injective function. -/
@[reducible]
protected def idemSemiring [IdemSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β]
    [NatCast β] [HasSup β] [Bot β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemSemiring β :=
  { hf.Semiring f zero one add mul nsmul npow nat_cast, hf.SemilatticeSup _ sup,
    ‹Bot β› with
    add_eq_sup := fun a b => hf <| by erw [sup, add, add_eq_sup]
    bot := ⊥
    bot_le := fun a => bot.trans_le <| @bot_le _ _ _ <| f a }
#align function.injective.idem_semiring Function.Injective.idemSemiring

/- warning: function.injective.idem_comm_semiring -> Function.Injective.idemCommSemiring is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : IdemCommSemiring.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : One.{u2} β] [_inst_4 : Add.{u2} β] [_inst_5 : Mul.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : SMul.{0, u2} Nat β] [_inst_8 : NatCast.{u2} β] [_inst_9 : HasSup.{u2} β] [_inst_10 : Bot.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1)))))))))) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_3)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1)))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_4) x y)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_5) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (SMul.smul.{0, u2} Nat β _inst_7 n x)) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))))))) n (f x))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1)))))) (f x) n)) -> (forall (n : Nat), Eq.{succ u1} α (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u2} Nat β (CoeTCₓ.coe.{1, succ u2} Nat β (Nat.castCoe.{u2} β _inst_8))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))))))))) n)) -> (forall (a : β) (b : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_9 a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))) (f a) (f b))) -> (Eq.{succ u1} α (f (Bot.bot.{u2} β _inst_10)) (Bot.bot.{u1} α (CanonicallyOrderedAddMonoid.toHasBot.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))))) -> (IdemCommSemiring.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : IdemCommSemiring.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : One.{u2} β] [_inst_4 : Add.{u2} β] [_inst_5 : Mul.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : SMul.{0, u2} Nat β] [_inst_8 : NatCast.{u2} β] [_inst_9 : HasSup.{u2} β] [_inst_10 : Bot.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (IdemCommSemiring.toCommSemiring.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_3))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1)))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_4) x y)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_5) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1)))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HSMul.hSMul.{0, u2, u2} Nat β β (instHSMul.{0, u2} Nat β _inst_7) n x)) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1)))))))) n (f x))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1)))))) (f x) n)) -> (forall (n : Nat), Eq.{succ u1} α (f (Nat.cast.{u2} β _inst_8 n)) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (IdemSemiring.toSemiring.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))) n)) -> (forall (a : β) (b : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_9 a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (IdemCommSemiring.toSemilatticeSup.{u1} α _inst_1)) (f a) (f b))) -> (Eq.{succ u1} α (f (Bot.bot.{u2} β _inst_10)) (Bot.bot.{u1} α (CanonicallyOrderedAddMonoid.toBot.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (IdemCommSemiring.toIdemSemiring.{u1} α _inst_1))))) -> (IdemCommSemiring.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.idem_comm_semiring Function.Injective.idemCommSemiringₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `idem_comm_semiring` instance along an injective function. -/
@[reducible]
protected def idemCommSemiring [IdemCommSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ]
    [SMul ℕ β] [NatCast β] [HasSup β] [Bot β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemCommSemiring β :=
  { hf.CommSemiring f zero one add mul nsmul npow nat_cast,
    hf.IdemSemiring f zero one add mul nsmul npow nat_cast sup bot with }
#align function.injective.idem_comm_semiring Function.Injective.idemCommSemiring

/- warning: function.injective.kleene_algebra -> Function.Injective.kleeneAlgebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : KleeneAlgebra.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : One.{u2} β] [_inst_4 : Add.{u2} β] [_inst_5 : Mul.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : SMul.{0, u2} Nat β] [_inst_8 : NatCast.{u2} β] [_inst_9 : HasSup.{u2} β] [_inst_10 : Bot.{u2} β] [_inst_11 : KStar.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))))))) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_3)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_4) x y)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_5) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (SMul.smul.{0, u2} Nat β _inst_7 n x)) (SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) n (f x))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (f x) n)) -> (forall (n : Nat), Eq.{succ u1} α (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u2} Nat β (CoeTCₓ.coe.{1, succ u2} Nat β (Nat.castCoe.{u2} β _inst_8))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))))) n)) -> (forall (a : β) (b : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_9 a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))) (f a) (f b))) -> (Eq.{succ u1} α (f (Bot.bot.{u2} β _inst_10)) (Bot.bot.{u1} α (CanonicallyOrderedAddMonoid.toHasBot.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) -> (forall (a : β), Eq.{succ u1} α (f (KStar.kstar.{u2} β _inst_11 a)) (KStar.kstar.{u1} α (KleeneAlgebra.toHasKstar.{u1} α _inst_1) (f a))) -> (KleeneAlgebra.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : KleeneAlgebra.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : One.{u2} β] [_inst_4 : Add.{u2} β] [_inst_5 : Mul.{u2} β] [_inst_6 : Pow.{u2, 0} β Nat] [_inst_7 : SMul.{0, u2} Nat β] [_inst_8 : NatCast.{u2} β] [_inst_9 : HasSup.{u2} β] [_inst_10 : Bot.{u2} β] [_inst_11 : KStar.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_3))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_4) x y)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_5) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HSMul.hSMul.{0, u2, u2} Nat β β (instHSMul.{0, u2} Nat β _inst_7) n x)) (HSMul.hSMul.{0, u1, u1} Nat α α (instHSMul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))))) n (f x))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_6) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1)))))) (f x) n)) -> (forall (n : Nat), Eq.{succ u1} α (f (Nat.cast.{u2} β _inst_8 n)) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (IdemSemiring.toSemiring.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))) n)) -> (forall (a : β) (b : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_9 a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (IdemSemiring.toSemilatticeSup.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))) (f a) (f b))) -> (Eq.{succ u1} α (f (Bot.bot.{u2} β _inst_10)) (Bot.bot.{u1} α (CanonicallyOrderedAddMonoid.toBot.{u1} α (IdemSemiring.toCanonicallyOrderedAddMonoid.{u1} α (KleeneAlgebra.toIdemSemiring.{u1} α _inst_1))))) -> (forall (a : β), Eq.{succ u1} α (f (KStar.kstar.{u2} β _inst_11 a)) (KStar.kstar.{u1} α (KleeneAlgebra.toKStar.{u1} α _inst_1) (f a))) -> (KleeneAlgebra.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.kleene_algebra Function.Injective.kleeneAlgebraₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `idem_comm_semiring` instance along an injective function. -/
@[reducible]
protected def kleeneAlgebra [KleeneAlgebra α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β]
    [NatCast β] [HasSup β] [Bot β] [KStar β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥)
    (kstar : ∀ a, f a∗ = (f a)∗) : KleeneAlgebra β :=
  { hf.IdemSemiring f zero one add mul nsmul npow nat_cast sup bot,
    ‹KStar
        β› with
    one_le_kstar := fun a =>
      one.trans_le <| by
        erw [kstar]
        exact one_le_kstar
    mul_kstar_le_kstar := fun a => by
      change f _ ≤ _
      erw [mul, kstar]
      exact mul_kstar_le_kstar
    kstar_mul_le_kstar := fun a => by
      change f _ ≤ _
      erw [mul, kstar]
      exact kstar_mul_le_kstar
    mul_kstar_le_self := fun a b (h : f _ ≤ _) =>
      by
      change f _ ≤ _
      erw [mul, kstar]
      erw [mul] at h
      exact mul_kstar_le_self h
    kstar_mul_le_self := fun a b (h : f _ ≤ _) =>
      by
      change f _ ≤ _
      erw [mul, kstar]
      erw [mul] at h
      exact kstar_mul_le_self h }
#align function.injective.kleene_algebra Function.Injective.kleeneAlgebra

end Function.Injective

