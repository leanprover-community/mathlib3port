/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module algebra.big_operators.ring
! leanprover-community/mathlib commit 327c3c0d9232d80e250dc8f65e7835b82b266ea5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Field.Defs
import Mathbin.Data.Finset.Pi
import Mathbin.Data.Finset.Powerset

/-!
# Results about big operators with values in a (semi)ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/


universe u v w

open BigOperators

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {b : β} {f g : α → β}

section CommMonoid

variable [CommMonoid β]

open Classical

#print Finset.prod_pow_eq_pow_sum /-
theorem prod_pow_eq_pow_sum {x : β} {f : α → ℕ} :
    ∀ {s : Finset α}, (∏ i in s, x ^ f i) = x ^ ∑ x in s, f x :=
  by
  apply Finset.induction
  · simp
  · intro a s has H
    rw [Finset.prod_insert has, Finset.sum_insert has, pow_add, H]
#align finset.prod_pow_eq_pow_sum Finset.prod_pow_eq_pow_sum
-/

end CommMonoid

section Semiring

variable [NonUnitalNonAssocSemiring β]

/- warning: finset.sum_mul -> Finset.sum_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {b : β} {f : α -> β} [_inst_1 : NonUnitalNonAssocSemiring.{u2} β], Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β _inst_1))) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β _inst_1) s (fun (x : α) => f x)) b) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β _inst_1) s (fun (x : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β _inst_1))) (f x) b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {b : β} {f : α -> β} [_inst_1 : NonUnitalNonAssocSemiring.{u2} β], Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (NonUnitalNonAssocSemiring.toMul.{u2} β _inst_1)) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β _inst_1) s (fun (x : α) => f x)) b) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β _inst_1) s (fun (x : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (NonUnitalNonAssocSemiring.toMul.{u2} β _inst_1)) (f x) b))
Case conversion may be inaccurate. Consider using '#align finset.sum_mul Finset.sum_mulₓ'. -/
theorem sum_mul : (∑ x in s, f x) * b = ∑ x in s, f x * b :=
  AddMonoidHom.map_sum (AddMonoidHom.mulRight b) _ s
#align finset.sum_mul Finset.sum_mul

/- warning: finset.mul_sum -> Finset.mul_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {b : β} {f : α -> β} [_inst_1 : NonUnitalNonAssocSemiring.{u2} β], Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β _inst_1))) b (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β _inst_1) s (fun (x : α) => f x))) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β _inst_1) s (fun (x : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β _inst_1))) b (f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {b : β} {f : α -> β} [_inst_1 : NonUnitalNonAssocSemiring.{u2} β], Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (NonUnitalNonAssocSemiring.toMul.{u2} β _inst_1)) b (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β _inst_1) s (fun (x : α) => f x))) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β _inst_1) s (fun (x : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (NonUnitalNonAssocSemiring.toMul.{u2} β _inst_1)) b (f x)))
Case conversion may be inaccurate. Consider using '#align finset.mul_sum Finset.mul_sumₓ'. -/
theorem mul_sum : (b * ∑ x in s, f x) = ∑ x in s, b * f x :=
  AddMonoidHom.map_sum (AddMonoidHom.mulLeft b) _ s
#align finset.mul_sum Finset.mul_sum

/- warning: finset.sum_mul_sum -> Finset.sum_mul_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} β] {ι₁ : Type.{u2}} {ι₂ : Type.{u3}} (s₁ : Finset.{u2} ι₁) (s₂ : Finset.{u3} ι₂) (f₁ : ι₁ -> β) (f₂ : ι₂ -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (Finset.sum.{u1, u2} β ι₁ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) s₁ (fun (x₁ : ι₁) => f₁ x₁)) (Finset.sum.{u1, u3} β ι₂ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) s₂ (fun (x₂ : ι₂) => f₂ x₂))) (Finset.sum.{u1, max u2 u3} β (Prod.{u2, u3} ι₁ ι₂) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.product.{u2, u3} ι₁ ι₂ s₁ s₂) (fun (p : Prod.{u2, u3} ι₁ ι₂) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (f₁ (Prod.fst.{u2, u3} ι₁ ι₂ p)) (f₂ (Prod.snd.{u2, u3} ι₁ ι₂ p))))
but is expected to have type
  forall {β : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} β] {ι₁ : Type.{u2}} {ι₂ : Type.{u1}} (s₁ : Finset.{u2} ι₁) (s₂ : Finset.{u1} ι₂) (f₁ : ι₁ -> β) (f₂ : ι₂ -> β), Eq.{succ u3} β (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (NonUnitalNonAssocSemiring.toMul.{u3} β _inst_1)) (Finset.sum.{u3, u2} β ι₁ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} β _inst_1) s₁ (fun (x₁ : ι₁) => f₁ x₁)) (Finset.sum.{u3, u1} β ι₂ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} β _inst_1) s₂ (fun (x₂ : ι₂) => f₂ x₂))) (Finset.sum.{u3, max u1 u2} β (Prod.{u2, u1} ι₁ ι₂) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} β _inst_1) (Finset.product.{u2, u1} ι₁ ι₂ s₁ s₂) (fun (p : Prod.{u2, u1} ι₁ ι₂) => HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (NonUnitalNonAssocSemiring.toMul.{u3} β _inst_1)) (f₁ (Prod.fst.{u2, u1} ι₁ ι₂ p)) (f₂ (Prod.snd.{u2, u1} ι₁ ι₂ p))))
Case conversion may be inaccurate. Consider using '#align finset.sum_mul_sum Finset.sum_mul_sumₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sum_mul_sum {ι₁ : Type _} {ι₂ : Type _} (s₁ : Finset ι₁) (s₂ : Finset ι₂) (f₁ : ι₁ → β)
    (f₂ : ι₂ → β) : ((∑ x₁ in s₁, f₁ x₁) * ∑ x₂ in s₂, f₂ x₂) = ∑ p in s₁ ×ˢ s₂, f₁ p.1 * f₂ p.2 :=
  by
  rw [sum_product, sum_mul, sum_congr rfl]
  intros
  rw [mul_sum]
#align finset.sum_mul_sum Finset.sum_mul_sum

end Semiring

section Semiring

variable [NonAssocSemiring β]

/- warning: finset.sum_mul_boole -> Finset.sum_mul_boole is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (f : α -> β) (a : α), Eq.{succ u2} β (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1)) s (fun (x : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1)))) (f x) (ite.{succ u2} β (Eq.{succ u1} α a x) (_inst_2 a x) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} β (NonAssocSemiring.toAddCommMonoidWithOne.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1))))))))) (ite.{succ u2} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a s) (f a) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (f : α -> β) (a : α), Eq.{succ u2} β (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1)) s (fun (x : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1))) (f x) (ite.{succ u2} β (Eq.{succ u1} α a x) (_inst_2 a x) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (NonAssocSemiring.toOne.{u2} β _inst_1))) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (MulZeroOneClass.toZero.{u2} β (NonAssocSemiring.toMulZeroOneClass.{u2} β _inst_1))))))) (ite.{succ u2} β (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a s) (f a) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (MulZeroOneClass.toZero.{u2} β (NonAssocSemiring.toMulZeroOneClass.{u2} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.sum_mul_boole Finset.sum_mul_booleₓ'. -/
theorem sum_mul_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∑ x in s, f x * ite (a = x) 1 0) = ite (a ∈ s) (f a) 0 := by simp
#align finset.sum_mul_boole Finset.sum_mul_boole

/- warning: finset.sum_boole_mul -> Finset.sum_boole_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (f : α -> β) (a : α), Eq.{succ u2} β (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1)) s (fun (x : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1)))) (ite.{succ u2} β (Eq.{succ u1} α a x) (_inst_2 a x) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} β (NonAssocSemiring.toAddCommMonoidWithOne.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1))))))) (f x))) (ite.{succ u2} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a s) (f a) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (f : α -> β) (a : α), Eq.{succ u2} β (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1)) s (fun (x : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_1))) (ite.{succ u2} β (Eq.{succ u1} α a x) (_inst_2 a x) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (NonAssocSemiring.toOne.{u2} β _inst_1))) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (MulZeroOneClass.toZero.{u2} β (NonAssocSemiring.toMulZeroOneClass.{u2} β _inst_1))))) (f x))) (ite.{succ u2} β (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a s) (f a) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (MulZeroOneClass.toZero.{u2} β (NonAssocSemiring.toMulZeroOneClass.{u2} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.sum_boole_mul Finset.sum_boole_mulₓ'. -/
theorem sum_boole_mul [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∑ x in s, ite (a = x) 1 0 * f x) = ite (a ∈ s) (f a) 0 := by simp
#align finset.sum_boole_mul Finset.sum_boole_mul

end Semiring

/- warning: finset.sum_div -> Finset.sum_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} β] {s : Finset.{u1} α} {f : α -> β} {b : β}, Eq.{succ u2} β (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivInvMonoid.toHasDiv.{u2} β (GroupWithZero.toDivInvMonoid.{u2} β (DivisionSemiring.toGroupWithZero.{u2} β _inst_1)))) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (DivisionSemiring.toSemiring.{u2} β _inst_1)))) s (fun (x : α) => f x)) b) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (DivisionSemiring.toSemiring.{u2} β _inst_1)))) s (fun (x : α) => HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivInvMonoid.toHasDiv.{u2} β (GroupWithZero.toDivInvMonoid.{u2} β (DivisionSemiring.toGroupWithZero.{u2} β _inst_1)))) (f x) b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} β] {s : Finset.{u1} α} {f : α -> β} {b : β}, Eq.{succ u2} β (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivisionSemiring.toDiv.{u2} β _inst_1)) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (DivisionSemiring.toSemiring.{u2} β _inst_1)))) s (fun (x : α) => f x)) b) (Finset.sum.{u2, u1} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (DivisionSemiring.toSemiring.{u2} β _inst_1)))) s (fun (x : α) => HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivisionSemiring.toDiv.{u2} β _inst_1)) (f x) b))
Case conversion may be inaccurate. Consider using '#align finset.sum_div Finset.sum_divₓ'. -/
theorem sum_div [DivisionSemiring β] {s : Finset α} {f : α → β} {b : β} :
    (∑ x in s, f x) / b = ∑ x in s, f x / b := by simp only [div_eq_mul_inv, sum_mul]
#align finset.sum_div Finset.sum_div

section CommSemiring

variable [CommSemiring β]

/- warning: finset.prod_sum -> Finset.prod_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommSemiring.{u2} β] {δ : α -> Type.{u3}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : forall (a : α), DecidableEq.{succ u3} (δ a)] {s : Finset.{u1} α} {t : forall (a : α), Finset.{u3} (δ a)} {f : forall (a : α), (δ a) -> β}, Eq.{succ u2} β (Finset.prod.{u2, u1} β α (CommSemiring.toCommMonoid.{u2} β _inst_1) s (fun (a : α) => Finset.sum.{u2, u3} β (δ a) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))) (t a) (fun (b : δ a) => f a b))) (Finset.sum.{u2, max u1 u3} β (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))) (Finset.pi.{u1, u3} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_2 a b) s t) (fun (p : forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) => Finset.prod.{u2, u1} β (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) (CommSemiring.toCommMonoid.{u2} β _inst_1) (Finset.attach.{u1} α s) (fun (x : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => f (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) x) (p (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) x) (Subtype.property.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CommSemiring.{u3} β] {δ : α -> Type.{u1}} [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : forall (a : α), DecidableEq.{succ u1} (δ a)] {s : Finset.{u2} α} {t : forall (a : α), Finset.{u1} (δ a)} {f : forall (a : α), (δ a) -> β}, Eq.{succ u3} β (Finset.prod.{u3, u2} β α (CommSemiring.toCommMonoid.{u3} β _inst_1) s (fun (a : α) => Finset.sum.{u3, u1} β (δ a) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (Semiring.toNonAssocSemiring.{u3} β (CommSemiring.toSemiring.{u3} β _inst_1)))) (t a) (fun (b : δ a) => f a b))) (Finset.sum.{u3, max u2 u1} β (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (Semiring.toNonAssocSemiring.{u3} β (CommSemiring.toSemiring.{u3} β _inst_1)))) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_2 a b) s t) (fun (p : forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)) => Finset.prod.{u3, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) (CommSemiring.toCommMonoid.{u3} β _inst_1) (Finset.attach.{u2} α s) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) x) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) x) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) x)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_sum Finset.prod_sumₓ'. -/
/-- The product over a sum can be written as a sum over the product of sets, `finset.pi`.
  `finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
theorem prod_sum {δ : α → Type _} [DecidableEq α] [∀ a, DecidableEq (δ a)] {s : Finset α}
    {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a → β} :
    (∏ a in s, ∑ b in t a, f a b) = ∑ p in s.pi t, ∏ x in s.attach, f x.1 (p x.1 x.2) :=
  by
  induction' s using Finset.induction with a s ha ih
  · rw [pi_empty, sum_singleton]
    rfl
  · have h₁ :
      ∀ x ∈ t a,
        ∀ y ∈ t a,
          ∀ h : x ≠ y, Disjoint (image (pi.cons s a x) (pi s t)) (image (pi.cons s a y) (pi s t)) :=
      by
      intro x hx y hy h
      simp only [disjoint_iff_ne, mem_image]
      rintro _ ⟨p₂, hp, eq₂⟩ _ ⟨p₃, hp₃, eq₃⟩ eq
      have : pi.cons s a x p₂ a (mem_insert_self _ _) = pi.cons s a y p₃ a (mem_insert_self _ _) :=
        by rw [eq₂, eq₃, Eq]
      rw [pi.cons_same, pi.cons_same] at this
      exact h this
    rw [prod_insert ha, pi_insert ha, ih, sum_mul, sum_bUnion h₁]
    refine' sum_congr rfl fun b _ => _
    have h₂ : ∀ p₁ ∈ pi s t, ∀ p₂ ∈ pi s t, pi.cons s a b p₁ = pi.cons s a b p₂ → p₁ = p₂ :=
      fun p₁ h₁ p₂ h₂ eq => pi_cons_injective ha Eq
    rw [sum_image h₂, mul_sum]
    refine' sum_congr rfl fun g _ => _
    rw [attach_insert, prod_insert, prod_image]
    · simp only [pi.cons_same]
      congr with ⟨v, hv⟩
      congr
      exact (pi.cons_ne (by rintro rfl <;> exact ha hv)).symm
    · exact fun _ _ _ _ => Subtype.eq ∘ Subtype.mk.inj
    · simp only [mem_image]
      rintro ⟨⟨_, hm⟩, _, rfl⟩
      exact ha hm
#align finset.prod_sum Finset.prod_sum

open Classical

/- warning: finset.prod_add -> Finset.prod_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommSemiring.{u2} β] (f : α -> β) (g : α -> β) (s : Finset.{u1} α), Eq.{succ u2} β (Finset.prod.{u2, u1} β α (CommSemiring.toCommMonoid.{u2} β _inst_1) s (fun (a : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))))) (f a) (g a))) (Finset.sum.{u2, u1} β (Finset.{u1} α) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))) (Finset.powerset.{u1} α s) (fun (t : Finset.{u1} α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))))) (Finset.prod.{u2, u1} β α (CommSemiring.toCommMonoid.{u2} β _inst_1) t (fun (a : α) => f a)) (Finset.prod.{u2, u1} β α (CommSemiring.toCommMonoid.{u2} β _inst_1) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => Classical.propDecidable (Eq.{succ u1} α a b))) s t) (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommSemiring.{u2} β] (f : α -> β) (g : α -> β) (s : Finset.{u1} α), Eq.{succ u2} β (Finset.prod.{u2, u1} β α (CommSemiring.toCommMonoid.{u2} β _inst_1) s (fun (a : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (Distrib.toAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))))) (f a) (g a))) (Finset.sum.{u2, u1} β (Finset.{u1} α) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1)))) (Finset.powerset.{u1} α s) (fun (t : Finset.{u1} α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (CommSemiring.toSemiring.{u2} β _inst_1))))) (Finset.prod.{u2, u1} β α (CommSemiring.toCommMonoid.{u2} β _inst_1) t (fun (a : α) => f a)) (Finset.prod.{u2, u1} β α (CommSemiring.toCommMonoid.{u2} β _inst_1) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => Classical.propDecidable (Eq.{succ u1} α a b))) s t) (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align finset.prod_add Finset.prod_addₓ'. -/
/-- The product of `f a + g a` over all of `s` is the sum
  over the powerset of `s` of the product of `f` over a subset `t` times
  the product of `g` over the complement of `t`  -/
theorem prod_add (f g : α → β) (s : Finset α) :
    (∏ a in s, f a + g a) = ∑ t in s.powerset, (∏ a in t, f a) * ∏ a in s \ t, g a :=
  calc
    (∏ a in s, f a + g a) =
        ∏ a in s, ∑ p in ({True, False} : Finset Prop), if p then f a else g a :=
      by simp
    _ =
        ∑ p in (s.pi fun _ => {True, False} : Finset (∀ a ∈ s, Prop)),
          ∏ a in s.attach, if p a.1 a.2 then f a.1 else g a.1 :=
      prod_sum
    _ = ∑ t in s.powerset, (∏ a in t, f a) * ∏ a in s \ t, g a :=
      by
      refine' Eq.symm (sum_bij (fun t _ a _ => a ∈ t) _ _ _ _)
      · simp [subset_iff] <;> tauto
      · intro t ht
        erw [prod_ite (fun a : { a // a ∈ s } => f a.1) fun a : { a // a ∈ s } => g a.1]
        refine'
                congr_arg₂ _
                  (prod_bij (fun (a : α) (ha : a ∈ t) => ⟨a, mem_powerset.1 ht ha⟩) _ _ _
                    fun b hb =>
                    ⟨b, by
                      cases b <;>
                        simpa only [true_and_iff, exists_prop, mem_filter, and_true_iff, mem_attach,
                          eq_self_iff_true, Subtype.coe_mk] using hb⟩)
                  (prod_bij (fun (a : α) (ha : a ∈ s \ t) => ⟨a, by simp_all⟩) _ _ _ fun b hb =>
                    ⟨b, by
                      cases b <;>
                        · simp only [true_and_iff, mem_filter, mem_attach, Subtype.coe_mk] at hb
                          simpa only [true_and_iff, exists_prop, and_true_iff, mem_sdiff,
                            eq_self_iff_true, Subtype.coe_mk, b_property] ⟩) <;>
              intros <;>
            simp_all <;>
          simp_all
      · intro a₁ a₂ h₁ h₂ H
        ext x
        simp only [Function.funext_iff, subset_iff, mem_powerset, eq_iff_iff] at h₁ h₂ H
        exact ⟨fun hx => (H x (h₁ hx)).1 hx, fun hx => (H x (h₂ hx)).2 hx⟩
      · intro f hf
        exact ⟨s.filter fun a : α => ∃ h : a ∈ s, f a h, by simp, by funext <;> intros <;> simp [*]⟩
    
#align finset.prod_add Finset.prod_add

/- warning: finset.prod_add_ordered -> Finset.prod_add_ordered is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] [_inst_3 : LinearOrder.{u1} ι] (s : Finset.{u1} ι) (f : ι -> R) (g : ι -> R), Eq.{succ u2} R (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R _inst_2) s (fun (i : ι) => HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) (f i) (g i))) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R _inst_2) s (fun (i : ι) => f i)) (Finset.sum.{u2, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))) s (fun (i : ι) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) (g i) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R _inst_2) (Finset.filter.{u1} ι (fun (_x : ι) => LT.lt.{u1} ι (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_3))))) _x i) (fun (a : ι) => LT.lt.decidable.{u1} ι _inst_3 a i) s) (fun (j : ι) => HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) (f j) (g j)))) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R _inst_2) (Finset.filter.{u1} ι (fun (j : ι) => LT.lt.{u1} ι (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_3))))) i j) (fun (a : ι) => LT.lt.decidable.{u1} ι _inst_3 i a) s) (fun (j : ι) => f j)))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_2 : CommSemiring.{u1} R] [_inst_3 : LinearOrder.{u2} ι] (s : Finset.{u2} ι) (f : ι -> R) (g : ι -> R), Eq.{succ u1} R (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R _inst_2) s (fun (i : ι) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))))) (f i) (g i))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))))) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R _inst_2) s (fun (i : ι) => f i)) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (g i) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R _inst_2) (Finset.filter.{u2} ι (fun (_x : ι) => LT.lt.{u2} ι (Preorder.toLT.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (DistribLattice.toLattice.{u2} ι (instDistribLattice.{u2} ι _inst_3)))))) _x i) (fun (a : ι) => instDecidableLtToLTToPreorderToPartialOrder.{u2} ι _inst_3 a i) s) (fun (j : ι) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))))) (f j) (g j)))) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R _inst_2) (Finset.filter.{u2} ι (fun (j : ι) => LT.lt.{u2} ι (Preorder.toLT.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (DistribLattice.toLattice.{u2} ι (instDistribLattice.{u2} ι _inst_3)))))) i j) (fun (a : ι) => instDecidableLtToLTToPreorderToPartialOrder.{u2} ι _inst_3 i a) s) (fun (j : ι) => f j)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_add_ordered Finset.prod_add_orderedₓ'. -/
/-- `∏ i, (f i + g i) = (∏ i, f i) + ∑ i, g i * (∏ j < i, f j + g j) * (∏ j > i, f j)`. -/
theorem prod_add_ordered {ι R : Type _} [CommSemiring R] [LinearOrder ι] (s : Finset ι)
    (f g : ι → R) :
    (∏ i in s, f i + g i) =
      (∏ i in s, f i) +
        ∑ i in s,
          (g i * ∏ j in s.filterₓ (· < i), f j + g j) * ∏ j in s.filterₓ fun j => i < j, f j :=
  by
  refine' Finset.induction_on_max s (by simp) _
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => (ha a ha').False
  rw [prod_insert ha', prod_insert ha', sum_insert ha', filter_insert, if_neg (lt_irrefl a),
    filter_true_of_mem ha, ihs, add_mul, mul_add, mul_add, add_assoc]
  congr 1
  rw [add_comm]
  congr 1
  · rw [filter_false_of_mem, prod_empty, mul_one]
    exact (forall_mem_insert _ _ _).2 ⟨lt_irrefl a, fun i hi => (ha i hi).not_lt⟩
  · rw [mul_sum]
    refine' sum_congr rfl fun i hi => _
    rw [filter_insert, if_neg (ha i hi).not_lt, filter_insert, if_pos (ha i hi), prod_insert,
      mul_left_comm]
    exact mt (fun ha => (mem_filter.1 ha).1) ha'
#align finset.prod_add_ordered Finset.prod_add_ordered

/- warning: finset.prod_sub_ordered -> Finset.prod_sub_ordered is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_2 : CommRing.{u2} R] [_inst_3 : LinearOrder.{u1} ι] (s : Finset.{u1} ι) (f : ι -> R) (g : ι -> R), Eq.{succ u2} R (Finset.prod.{u2, u1} R ι (CommRing.toCommMonoid.{u2} R _inst_2) s (fun (i : ι) => HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))) (f i) (g i))) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))) (Finset.prod.{u2, u1} R ι (CommRing.toCommMonoid.{u2} R _inst_2) s (fun (i : ι) => f i)) (Finset.sum.{u2, u1} R ι (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))) s (fun (i : ι) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (CommRing.toRing.{u2} R _inst_2)))) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (CommRing.toRing.{u2} R _inst_2)))) (g i) (Finset.prod.{u2, u1} R ι (CommRing.toCommMonoid.{u2} R _inst_2) (Finset.filter.{u1} ι (fun (_x : ι) => LT.lt.{u1} ι (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_3))))) _x i) (fun (a : ι) => LT.lt.decidable.{u1} ι _inst_3 a i) s) (fun (j : ι) => HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))) (f j) (g j)))) (Finset.prod.{u2, u1} R ι (CommRing.toCommMonoid.{u2} R _inst_2) (Finset.filter.{u1} ι (fun (j : ι) => LT.lt.{u1} ι (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_3))))) i j) (fun (a : ι) => LT.lt.decidable.{u1} ι _inst_3 i a) s) (fun (j : ι) => f j)))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] [_inst_3 : LinearOrder.{u2} ι] (s : Finset.{u2} ι) (f : ι -> R) (g : ι -> R), Eq.{succ u1} R (Finset.prod.{u1, u2} R ι (CommRing.toCommMonoid.{u1} R _inst_2) s (fun (i : ι) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_2))) (f i) (g i))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Finset.prod.{u1, u2} R ι (CommRing.toCommMonoid.{u1} R _inst_2) s (fun (i : ι) => f i)) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (g i) (Finset.prod.{u1, u2} R ι (CommRing.toCommMonoid.{u1} R _inst_2) (Finset.filter.{u2} ι (fun (_x : ι) => LT.lt.{u2} ι (Preorder.toLT.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (DistribLattice.toLattice.{u2} ι (instDistribLattice.{u2} ι _inst_3)))))) _x i) (fun (a : ι) => instDecidableLtToLTToPreorderToPartialOrder.{u2} ι _inst_3 a i) s) (fun (j : ι) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_2))) (f j) (g j)))) (Finset.prod.{u1, u2} R ι (CommRing.toCommMonoid.{u1} R _inst_2) (Finset.filter.{u2} ι (fun (j : ι) => LT.lt.{u2} ι (Preorder.toLT.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (DistribLattice.toLattice.{u2} ι (instDistribLattice.{u2} ι _inst_3)))))) i j) (fun (a : ι) => instDecidableLtToLTToPreorderToPartialOrder.{u2} ι _inst_3 i a) s) (fun (j : ι) => f j)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_sub_ordered Finset.prod_sub_orderedₓ'. -/
/-- `∏ i, (f i - g i) = (∏ i, f i) - ∑ i, g i * (∏ j < i, f j - g j) * (∏ j > i, f j)`. -/
theorem prod_sub_ordered {ι R : Type _} [CommRing R] [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    (∏ i in s, f i - g i) =
      (∏ i in s, f i) -
        ∑ i in s,
          (g i * ∏ j in s.filterₓ (· < i), f j - g j) * ∏ j in s.filterₓ fun j => i < j, f j :=
  by
  simp only [sub_eq_add_neg]
  convert prod_add_ordered s f fun i => -g i
  simp
#align finset.prod_sub_ordered Finset.prod_sub_ordered

/- warning: finset.prod_one_sub_ordered -> Finset.prod_one_sub_ordered is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_2 : CommRing.{u2} R] [_inst_3 : LinearOrder.{u1} ι] (s : Finset.{u1} ι) (f : ι -> R), Eq.{succ u2} R (Finset.prod.{u2, u1} R ι (CommRing.toCommMonoid.{u2} R _inst_2) s (fun (i : ι) => HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2)))))))) (f i))) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2)))))))) (Finset.sum.{u2, u1} R ι (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))) s (fun (i : ι) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (Ring.toDistrib.{u2} R (CommRing.toRing.{u2} R _inst_2)))) (f i) (Finset.prod.{u2, u1} R ι (CommRing.toCommMonoid.{u2} R _inst_2) (Finset.filter.{u1} ι (fun (_x : ι) => LT.lt.{u1} ι (Preorder.toLT.{u1} ι (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_3))))) _x i) (fun (a : ι) => LT.lt.decidable.{u1} ι _inst_3 a i) s) (fun (j : ι) => HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2)))))))) (f j))))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] [_inst_3 : LinearOrder.{u2} ι] (s : Finset.{u2} ι) (f : ι -> R), Eq.{succ u1} R (Finset.prod.{u1, u2} R ι (CommRing.toCommMonoid.{u1} R _inst_2) s (fun (i : ι) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_2))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (f i))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_2))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (f i) (Finset.prod.{u1, u2} R ι (CommRing.toCommMonoid.{u1} R _inst_2) (Finset.filter.{u2} ι (fun (_x : ι) => LT.lt.{u2} ι (Preorder.toLT.{u2} ι (PartialOrder.toPreorder.{u2} ι (SemilatticeInf.toPartialOrder.{u2} ι (Lattice.toSemilatticeInf.{u2} ι (DistribLattice.toLattice.{u2} ι (instDistribLattice.{u2} ι _inst_3)))))) _x i) (fun (a : ι) => instDecidableLtToLTToPreorderToPartialOrder.{u2} ι _inst_3 a i) s) (fun (j : ι) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_2))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (f j))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_one_sub_ordered Finset.prod_one_sub_orderedₓ'. -/
/-- `∏ i, (1 - f i) = 1 - ∑ i, f i * (∏ j < i, 1 - f j)`. This formula is useful in construction of
a partition of unity from a collection of “bump” functions.  -/
theorem prod_one_sub_ordered {ι R : Type _} [CommRing R] [LinearOrder ι] (s : Finset ι)
    (f : ι → R) : (∏ i in s, 1 - f i) = 1 - ∑ i in s, f i * ∏ j in s.filterₓ (· < i), 1 - f j :=
  by
  rw [prod_sub_ordered]
  simp
#align finset.prod_one_sub_ordered Finset.prod_one_sub_ordered

/- warning: finset.sum_pow_mul_eq_add_pow -> Finset.sum_pow_mul_eq_add_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] (a : R) (b : R) (s : Finset.{u1} α), Eq.{succ u2} R (Finset.sum.{u2, u1} R (Finset.{u1} α) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))) (Finset.powerset.{u1} α s) (fun (t : Finset.{u1} α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))))) a (Finset.card.{u1} α t)) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))))) b (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.card.{u1} α s) (Finset.card.{u1} α t))))) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))))) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) a b) (Finset.card.{u1} α s))
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u1}} [_inst_2 : CommSemiring.{u1} R] (a : R) (b : R) (s : Finset.{u2} α), Eq.{succ u1} R (Finset.sum.{u1, u2} R (Finset.{u2} α) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))) (Finset.powerset.{u2} α s) (fun (t : Finset.{u2} α) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) a (Finset.card.{u2} α t)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) b (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.card.{u2} α s) (Finset.card.{u2} α t))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))))) a b) (Finset.card.{u2} α s))
Case conversion may be inaccurate. Consider using '#align finset.sum_pow_mul_eq_add_pow Finset.sum_pow_mul_eq_add_powₓ'. -/
/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a `finset`
gives `(a + b)^s.card`.-/
theorem sum_pow_mul_eq_add_pow {α R : Type _} [CommSemiring R] (a b : R) (s : Finset α) :
    (∑ t in s.powerset, a ^ t.card * b ^ (s.card - t.card)) = (a + b) ^ s.card :=
  by
  rw [← prod_const, prod_add]
  refine' Finset.sum_congr rfl fun t ht => _
  rw [prod_const, prod_const, ← card_sdiff (mem_powerset.1 ht)]
#align finset.sum_pow_mul_eq_add_pow Finset.sum_pow_mul_eq_add_pow

#print Finset.dvd_sum /-
theorem dvd_sum {b : β} {s : Finset α} {f : α → β} (h : ∀ x ∈ s, b ∣ f x) : b ∣ ∑ x in s, f x :=
  Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩ <;> exact h x hx
#align finset.dvd_sum Finset.dvd_sum
-/

#print Finset.prod_natCast /-
@[norm_cast]
theorem prod_natCast (s : Finset α) (f : α → ℕ) : ↑(∏ x in s, f x : ℕ) = ∏ x in s, (f x : β) :=
  (Nat.castRingHom β).map_prod f s
#align finset.prod_nat_cast Finset.prod_natCast
-/

end CommSemiring

section CommRing

variable {R : Type _} [CommRing R]

/- warning: finset.prod_range_cast_nat_sub -> Finset.prod_range_cast_nat_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (n : Nat) (k : Nat), Eq.{succ u1} R (Finset.prod.{u1, 0} R Nat (CommRing.toCommMonoid.{u1} R _inst_1) (Finset.range k) (fun (i : Nat) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) n) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) i))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) (Finset.prod.{0, 0} Nat Nat Nat.commMonoid (Finset.range k) (fun (i : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n i)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (n : Nat) (k : Nat), Eq.{succ u1} R (Finset.prod.{u1, 0} R Nat (CommRing.toCommMonoid.{u1} R _inst_1) (Finset.range k) (fun (i : Nat) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Nat.cast.{u1} R (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) n) (Nat.cast.{u1} R (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) i))) (Nat.cast.{u1} R (NonAssocRing.toNatCast.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Finset.prod.{0, 0} Nat Nat Nat.commMonoid (Finset.range k) (fun (i : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_cast_nat_sub Finset.prod_range_cast_nat_subₓ'. -/
theorem prod_range_cast_nat_sub (n k : ℕ) :
    (∏ i in range k, (n - i : R)) = (∏ i in range k, n - i : ℕ) :=
  by
  rw [prod_nat_cast]
  cases' le_or_lt k n with hkn hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp
#align finset.prod_range_cast_nat_sub Finset.prod_range_cast_nat_sub

end CommRing

/- warning: finset.prod_powerset_insert -> Finset.prod_powerset_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommMonoid.{u2} β] {s : Finset.{u1} α} {x : α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) -> (forall (f : (Finset.{u1} α) -> β), Eq.{succ u2} β (Finset.prod.{u2, u1} β (Finset.{u1} α) _inst_2 (Finset.powerset.{u1} α (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x s)) (fun (a : Finset.{u1} α) => f a)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)))) (Finset.prod.{u2, u1} β (Finset.{u1} α) _inst_2 (Finset.powerset.{u1} α s) (fun (a : Finset.{u1} α) => f a)) (Finset.prod.{u2, u1} β (Finset.{u1} α) _inst_2 (Finset.powerset.{u1} α s) (fun (t : Finset.{u1} α) => f (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x t)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommMonoid.{u2} β] {s : Finset.{u1} α} {x : α}, (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) -> (forall (f : (Finset.{u1} α) -> β), Eq.{succ u2} β (Finset.prod.{u2, u1} β (Finset.{u1} α) _inst_2 (Finset.powerset.{u1} α (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x s)) (fun (a : Finset.{u1} α) => f a)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)))) (Finset.prod.{u2, u1} β (Finset.{u1} α) _inst_2 (Finset.powerset.{u1} α s) (fun (a : Finset.{u1} α) => f a)) (Finset.prod.{u2, u1} β (Finset.{u1} α) _inst_2 (Finset.powerset.{u1} α s) (fun (t : Finset.{u1} α) => f (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x t)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_powerset_insert Finset.prod_powerset_insertₓ'. -/
/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive
      "A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all subsets\nof `s`, and over all subsets of `s` to which one adds `x`."]
theorem prod_powerset_insert [DecidableEq α] [CommMonoid β] {s : Finset α} {x : α} (h : x ∉ s)
    (f : Finset α → β) :
    (∏ a in (insert x s).powerset, f a) =
      (∏ a in s.powerset, f a) * ∏ t in s.powerset, f (insert x t) :=
  by
  rw [powerset_insert, Finset.prod_union, Finset.prod_image]
  · intro t₁ h₁ t₂ h₂ heq
    rw [← Finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₁ h), ←
      Finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₂ h), HEq]
  · rw [Finset.disjoint_iff_ne]
    intro t₁ h₁ t₂ h₂
    rcases Finset.mem_image.1 h₂ with ⟨t₃, h₃, H₃₂⟩
    rw [← H₃₂]
    exact ne_insert_of_not_mem _ _ (not_mem_of_mem_powerset_of_not_mem h₁ h)
#align finset.prod_powerset_insert Finset.prod_powerset_insert
#align finset.sum_powerset_insert Finset.sum_powerset_insert

#print Finset.prod_powerset /-
/-- A product over `powerset s` is equal to the double product over sets of subsets of `s` with
`card s = k`, for `k = 1, ..., card s`. -/
@[to_additive
      "A sum over `powerset s` is equal to the double sum over sets of subsets of `s` with\n`card s = k`, for `k = 1, ..., card s`"]
theorem prod_powerset [CommMonoid β] (s : Finset α) (f : Finset α → β) :
    (∏ t in powerset s, f t) = ∏ j in range (card s + 1), ∏ t in powersetLen j s, f t := by
  rw [powerset_card_disj_Union, prod_disj_Union]
#align finset.prod_powerset Finset.prod_powerset
#align finset.sum_powerset Finset.sum_powerset
-/

/- warning: finset.sum_range_succ_mul_sum_range_succ -> Finset.sum_range_succ_mul_sum_range_succ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} β] (n : Nat) (k : Nat) (f : Nat -> β) (g : Nat -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => f i)) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => g i))) (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toHasAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toHasAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toHasAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range n) (fun (i : Nat) => f i)) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range k) (fun (i : Nat) => g i))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (f n) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range k) (fun (i : Nat) => g i)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range n) (fun (i : Nat) => f i)) (g k))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (f n) (g k)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} β] (n : Nat) (k : Nat) (f : Nat -> β) (g : Nat -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1)) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => f i)) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => g i))) (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1)) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range n) (fun (i : Nat) => f i)) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range k) (fun (i : Nat) => g i))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1)) (f n) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range k) (fun (i : Nat) => g i)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1)) (Finset.sum.{u1, 0} β Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) (Finset.range n) (fun (i : Nat) => f i)) (g k))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1)) (f n) (g k)))
Case conversion may be inaccurate. Consider using '#align finset.sum_range_succ_mul_sum_range_succ Finset.sum_range_succ_mul_sum_range_succₓ'. -/
theorem sum_range_succ_mul_sum_range_succ [NonUnitalNonAssocSemiring β] (n k : ℕ) (f g : ℕ → β) :
    ((∑ i in range (n + 1), f i) * ∑ i in range (k + 1), g i) =
      (((∑ i in range n, f i) * ∑ i in range k, g i) + f n * ∑ i in range k, g i) +
          (∑ i in range n, f i) * g k +
        f n * g k :=
  by simp only [add_mul, mul_add, add_assoc, sum_range_succ]
#align finset.sum_range_succ_mul_sum_range_succ Finset.sum_range_succ_mul_sum_range_succ

end Finset

