/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module algebra.order.ring.with_top
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Ring
import Mathbin.Algebra.Order.Monoid.WithTop
import Mathbin.Algebra.Order.Ring.Canonical

/-! # Structures involving `*` and `0` on `with_top` and `with_bot`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main results of this section are `with_top.canonically_ordered_comm_semiring` and
`with_bot.ordered_comm_semiring`.
-/


variable {α : Type _}

namespace WithTop

instance [Nonempty α] : Nontrivial (WithTop α) :=
  Option.nontrivial

variable [DecidableEq α]

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithTop α) where
  zero := 0
  mul m n := if m = 0 ∨ n = 0 then 0 else Option.map₂ (· * ·) m n
  zero_mul a := if_pos <| Or.inl rfl
  mul_zero a := if_pos <| Or.inr rfl

/- warning: with_top.mul_def -> WithTop.mul_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α}, Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) a b) (ite.{succ u1} (WithTop.{u1} α) (Or (Eq.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))))) (Eq.{succ u1} (WithTop.{u1} α) b (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))))) (Or.decidable (Eq.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))))) (Eq.{succ u1} (WithTop.{u1} α) b (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))))) (Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))))) (Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) b (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))))) (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))) (Option.map₂.{u1, u1, u1} α α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_3)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α}, Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) a b) (ite.{succ u1} (WithTop.{u1} α) (Or (Eq.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))) (Eq.{succ u1} (WithTop.{u1} α) b (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))))) (instDecidableOr (Eq.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))) (Eq.{succ u1} (WithTop.{u1} α) b (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))) (WithTop.instDecidableEqWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))) (WithTop.instDecidableEqWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) b (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))))) (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))) (Option.map₂.{u1, u1, u1} α α α (fun (x._@.Mathlib.Algebra.Order.Ring.WithTop._hyg.211 : α) (x._@.Mathlib.Algebra.Order.Ring.WithTop._hyg.213 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_3) x._@.Mathlib.Algebra.Order.Ring.WithTop._hyg.211 x._@.Mathlib.Algebra.Order.Ring.WithTop._hyg.213) a b))
Case conversion may be inaccurate. Consider using '#align with_top.mul_def WithTop.mul_defₓ'. -/
theorem mul_def {a b : WithTop α} : a * b = if a = 0 ∨ b = 0 then 0 else Option.map₂ (· * ·) a b :=
  rfl
#align with_top.mul_def WithTop.mul_def

/- warning: with_top.mul_top -> WithTop.mul_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithTop.{u1} α}, (Ne.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))))) -> (Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithTop.{u1} α}, (Ne.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))) -> (Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))
Case conversion may be inaccurate. Consider using '#align with_top.mul_top WithTop.mul_topₓ'. -/
@[simp]
theorem mul_top {a : WithTop α} (h : a ≠ 0) : a * ⊤ = ⊤ := by cases a <;> simp [mul_def, h] <;> rfl
#align with_top.mul_top WithTop.mul_top

/- warning: with_top.top_mul -> WithTop.top_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithTop.{u1} α}, (Ne.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2))))) -> (Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)) a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithTop.{u1} α}, (Ne.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α _inst_2)))) -> (Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)) a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))
Case conversion may be inaccurate. Consider using '#align with_top.top_mul WithTop.top_mulₓ'. -/
@[simp]
theorem top_mul {a : WithTop α} (h : a ≠ 0) : ⊤ * a = ⊤ := by cases a <;> simp [mul_def, h] <;> rfl
#align with_top.top_mul WithTop.top_mul

/- warning: with_top.top_mul_top -> WithTop.top_mul_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α], Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α], Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))
Case conversion may be inaccurate. Consider using '#align with_top.top_mul_top WithTop.top_mul_topₓ'. -/
@[simp]
theorem top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ :=
  top_mul top_ne_zero
#align with_top.top_mul_top WithTop.top_mul_top

instance [NoZeroDivisors α] : NoZeroDivisors (WithTop α) :=
  by
  refine' ⟨fun a b h₁ => Decidable.by_contradiction fun h₂ => _⟩
  rw [mul_def, if_neg h₂] at h₁
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, rfl : _ = _, rfl : _ = _, hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

end Mul

section MulZeroClass

variable [MulZeroClass α]

/- warning: with_top.coe_mul -> WithTop.coe_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {a : α} {b : α}, Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) a b)) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {a : α} {b : α}, Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) a b)) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) (WithTop.some.{u1} α a) (WithTop.some.{u1} α b))
Case conversion may be inaccurate. Consider using '#align with_top.coe_mul WithTop.coe_mulₓ'. -/
@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithTop α) = a * b :=
  Decidable.byCases (fun this : a = 0 => by simp [this]) fun ha =>
    Decidable.byCases (fun this : b = 0 => by simp [this]) fun hb => by simp [*, mul_def]
#align with_top.coe_mul WithTop.coe_mul

/- warning: with_top.mul_coe -> WithTop.mul_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {b : α}, (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))) -> (forall {a : WithTop.{u1} α}, Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) b)) (Option.bind.{u1, u1} α α a (fun (a : α) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {b : α}, (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))) -> (forall {a : WithTop.{u1} α}, Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) a (WithTop.some.{u1} α b)) (Option.bind.{u1, u1} α α a (fun (a : α) => Option.some.{u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) a b))))
Case conversion may be inaccurate. Consider using '#align with_top.mul_coe WithTop.mul_coeₓ'. -/
theorem mul_coe {b : α} (hb : b ≠ 0) : ∀ {a : WithTop α}, a * b = a.bind fun a : α => ↑(a * b)
  | none =>
    show (if (⊤ : WithTop α) = 0 ∨ (b : WithTop α) = 0 then 0 else ⊤ : WithTop α) = ⊤ by simp [hb]
  | some a => show ↑a * ↑b = ↑(a * b) from coe_mul.symm
#align with_top.mul_coe WithTop.mul_coe

/- warning: with_top.mul_eq_top_iff -> WithTop.mul_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α}, Iff (Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) a b) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Or (And (Ne.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2)))))) (Eq.{succ u1} (WithTop.{u1} α) b (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) (And (Eq.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Ne.{succ u1} (WithTop.{u1} α) b (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (OfNat.mk.{u1} (WithTop.{u1} α) 0 (Zero.zero.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α}, Iff (Eq.{succ u1} (WithTop.{u1} α) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) a b) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (Or (And (Ne.{succ u1} (WithTop.{u1} α) a (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_2))))) (Eq.{succ u1} (WithTop.{u1} α) b (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))) (And (Eq.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (Ne.{succ u1} (WithTop.{u1} α) b (OfNat.ofNat.{u1} (WithTop.{u1} α) 0 (Zero.toOfNat0.{u1} (WithTop.{u1} α) (WithTop.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align with_top.mul_eq_top_iff WithTop.mul_eq_top_iffₓ'. -/
@[simp]
theorem mul_eq_top_iff {a b : WithTop α} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 :=
  by
  cases a <;> cases b <;> simp only [none_eq_top, some_eq_coe]
  · simp [← coe_mul]
  · by_cases hb : b = 0 <;> simp [hb]
  · by_cases ha : a = 0 <;> simp [ha]
  · simp [← coe_mul]
#align with_top.mul_eq_top_iff WithTop.mul_eq_top_iff

/- warning: with_top.mul_lt_top -> WithTop.mul_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] [_inst_3 : Preorder.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α}, (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (Ne.{succ u1} (WithTop.{u1} α) b (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_3)) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) a b) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] [_inst_3 : Preorder.{u1} α] {a : WithTop.{u1} α} {b : WithTop.{u1} α}, (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (Ne.{succ u1} (WithTop.{u1} α) b (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_3)) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) a b) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))
Case conversion may be inaccurate. Consider using '#align with_top.mul_lt_top WithTop.mul_lt_topₓ'. -/
theorem mul_lt_top [Preorder α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ :=
  by
  lift a to α using ha
  lift b to α using hb
  simp only [← coe_mul, coe_lt_top]
#align with_top.mul_lt_top WithTop.mul_lt_top

/- warning: with_top.untop'_zero_mul -> WithTop.untop'_zero_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] (a : WithTop.{u1} α) (b : WithTop.{u1} α), Eq.{succ u1} α (WithTop.untop'.{u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2)))) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toHasMul.{u1} (WithTop.{u1} α) (WithTop.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) (WithTop.untop'.{u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2)))) a) (WithTop.untop'.{u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2)))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] (a : WithTop.{u1} α) (b : WithTop.{u1} α), Eq.{succ u1} α (WithTop.untop'.{u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2))) (HMul.hMul.{u1, u1, u1} (WithTop.{u1} α) (WithTop.{u1} α) (WithTop.{u1} α) (instHMul.{u1} (WithTop.{u1} α) (MulZeroClass.toMul.{u1} (WithTop.{u1} α) (WithTop.instMulZeroClassWithTop.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) (WithTop.untop'.{u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2))) a) (WithTop.untop'.{u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2))) b))
Case conversion may be inaccurate. Consider using '#align with_top.untop'_zero_mul WithTop.untop'_zero_mulₓ'. -/
@[simp]
theorem untop'_zero_mul (a b : WithTop α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 :=
  by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untop'_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untop'_coe, mul_zero]
  induction a using WithTop.recTopCoe; · rw [top_mul hb, untop'_top, zero_mul]
  induction b using WithTop.recTopCoe; · rw [mul_top ha, untop'_top, mul_zero]
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]
#align with_top.untop'_zero_mul WithTop.untop'_zero_mul

end MulZeroClass

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) :=
  { WithTop.mulZeroClass with
    mul := (· * ·)
    one := 1
    zero := 0
    one_mul := fun a =>
      match a with
      | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
    mul_one := fun a =>
      match a with
      | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, mul_one] }

/- warning: monoid_with_zero_hom.with_top_map -> WithTop.MonoidWithZeroHom.withTopMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : MulZeroOneClass.{u1} R] [_inst_3 : DecidableEq.{succ u1} R] [_inst_4 : Nontrivial.{u1} R] [_inst_5 : MulZeroOneClass.{u2} S] [_inst_6 : DecidableEq.{succ u2} S] [_inst_7 : Nontrivial.{u2} S] (f : MonoidWithZeroHom.{u1, u2} R S _inst_2 _inst_5), (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} R S _inst_2 _inst_5) (fun (_x : MonoidWithZeroHom.{u1, u2} R S _inst_2 _inst_5) => R -> S) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} R S _inst_2 _inst_5) f)) -> (MonoidWithZeroHom.{u1, u2} (WithTop.{u1} R) (WithTop.{u2} S) (WithTop.mulZeroOneClass.{u1} R (fun (a : R) (b : R) => _inst_3 a b) _inst_2 _inst_4) (WithTop.mulZeroOneClass.{u2} S (fun (a : S) (b : S) => _inst_6 a b) _inst_5 _inst_7))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : MulZeroOneClass.{u1} R] [_inst_3 : DecidableEq.{succ u1} R] [_inst_4 : Nontrivial.{u1} R] [_inst_5 : MulZeroOneClass.{u2} S] [_inst_6 : DecidableEq.{succ u2} S] [_inst_7 : Nontrivial.{u2} S] (f : MonoidWithZeroHom.{u1, u2} R S _inst_2 _inst_5), (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidWithZeroHom.{u1, u2} R S _inst_2 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidWithZeroHom.{u1, u2} R S _inst_2 _inst_5) R S (MulOneClass.toMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_2)) (MulOneClass.toMul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S _inst_5)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidWithZeroHom.{u1, u2} R S _inst_2 _inst_5) R S (MulZeroOneClass.toMulOneClass.{u1} R _inst_2) (MulZeroOneClass.toMulOneClass.{u2} S _inst_5) (MonoidWithZeroHomClass.toMonoidHomClass.{max u1 u2, u1, u2} (MonoidWithZeroHom.{u1, u2} R S _inst_2 _inst_5) R S _inst_2 _inst_5 (MonoidWithZeroHom.monoidWithZeroHomClass.{u1, u2} R S _inst_2 _inst_5)))) f)) -> (MonoidWithZeroHom.{u1, u2} (WithTop.{u1} R) (WithTop.{u2} S) (WithTop.instMulZeroOneClassWithTop.{u1} R (fun (a : R) (b : R) => _inst_3 a b) _inst_2 _inst_4) (WithTop.instMulZeroOneClassWithTop.{u2} S (fun (a : S) (b : S) => _inst_6 a b) _inst_5 _inst_7))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.with_top_map WithTop.MonoidWithZeroHom.withTopMapₓ'. -/
/-- A version of `with_top.map` for `monoid_with_zero_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def WithTop.MonoidWithZeroHom.withTopMap {R S : Type _} [MulZeroOneClass R]
    [DecidableEq R] [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S)
    (hf : Function.Injective f) : WithTop R →*₀ WithTop S :=
  { f.toZeroHom.withTopMap,
    f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y =>
      by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.to_zero_hom.with_top_map.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      induction x using WithTop.recTopCoe
      · simp [hy, this]
      induction y using WithTop.recTopCoe
      · have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [hx, this]
      simp [← coe_mul] }
#align monoid_with_zero_hom.with_top_map WithTop.MonoidWithZeroHom.withTopMap

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithTop α) :=
  { WithTop.mulZeroClass with
    mul := (· * ·)
    zero := 0
    mul_assoc := fun a b c => by
      rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
      rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
      rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
      induction a using WithTop.recTopCoe; · simp [hb, hc]
      induction b using WithTop.recTopCoe; · simp [ha, hc]
      induction c using WithTop.recTopCoe; · simp [ha, hb]
      simp only [← coe_mul, mul_assoc] }

instance [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZero (WithTop α) :=
  { WithTop.mulZeroOneClass, WithTop.semigroupWithZero with }

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) :=
  { WithTop.monoidWithZero with
    mul := (· * ·)
    zero := 0
    mul_comm := fun a b => by
      simp only [or_comm', mul_def, mul_comm, @option.map₂_comm _ _ _ _ a b _ mul_comm] }

variable [CanonicallyOrderedCommSemiring α]

private theorem distrib' (a b c : WithTop α) : (a + b) * c = a * c + b * c :=
  by
  induction c using WithTop.recTopCoe
  · by_cases ha : a = 0 <;> simp [ha]
  · by_cases hc : c = 0
    · simp [hc]
    simp [mul_coe hc]
    cases a <;> cases b
    repeat' first |rfl|exact congr_arg some (add_mul _ _ _)
#align with_top.distrib' with_top.distrib'

/-- This instance requires `canonically_ordered_comm_semiring` as it is the smallest class
that derives from both `non_assoc_non_unital_semiring` and `canonically_ordered_add_monoid`, both
of which are required for distributivity. -/
instance [Nontrivial α] : CommSemiring (WithTop α) :=
  { WithTop.addCommMonoidWithOne,
    WithTop.commMonoidWithZero with
    right_distrib := distrib'
    left_distrib := fun a b c =>
      by
      rw [mul_comm, distrib', mul_comm b, mul_comm c]
      rfl }

instance [Nontrivial α] : CanonicallyOrderedCommSemiring (WithTop α) :=
  { WithTop.commSemiring, WithTop.canonicallyOrderedAddMonoid, WithTop.noZeroDivisors with }

/- warning: ring_hom.with_top_map -> WithTop.RingHom.withTopMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_3 : CanonicallyOrderedCommSemiring.{u1} R] [_inst_4 : DecidableEq.{succ u1} R] [_inst_5 : Nontrivial.{u1} R] [_inst_6 : CanonicallyOrderedCommSemiring.{u2} S] [_inst_7 : DecidableEq.{succ u2} S] [_inst_8 : Nontrivial.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))), (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))) f)) -> (RingHom.{u1, u2} (WithTop.{u1} R) (WithTop.{u2} S) (Semiring.toNonAssocSemiring.{u1} (WithTop.{u1} R) (OrderedSemiring.toSemiring.{u1} (WithTop.{u1} R) (OrderedCommSemiring.toOrderedSemiring.{u1} (WithTop.{u1} R) (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} (WithTop.{u1} R) (WithTop.canonicallyOrderedCommSemiring.{u1} R (fun (a : R) (b : R) => _inst_4 a b) _inst_3 _inst_5))))) (Semiring.toNonAssocSemiring.{u2} (WithTop.{u2} S) (OrderedSemiring.toSemiring.{u2} (WithTop.{u2} S) (OrderedCommSemiring.toOrderedSemiring.{u2} (WithTop.{u2} S) (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} (WithTop.{u2} S) (WithTop.canonicallyOrderedCommSemiring.{u2} S (fun (a : S) (b : S) => _inst_7 a b) _inst_6 _inst_8))))))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_3 : CanonicallyOrderedCommSemiring.{u1} R] [_inst_4 : DecidableEq.{succ u1} R] [_inst_5 : Nontrivial.{u1} R] [_inst_6 : CanonicallyOrderedCommSemiring.{u2} S] [_inst_7 : DecidableEq.{succ u2} S] [_inst_8 : Nontrivial.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))), (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6)))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6))))) R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6)))) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_3)))) (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} S _inst_6)))))))) f)) -> (RingHom.{u1, u2} (WithTop.{u1} R) (WithTop.{u2} S) (Semiring.toNonAssocSemiring.{u1} (WithTop.{u1} R) (OrderedSemiring.toSemiring.{u1} (WithTop.{u1} R) (OrderedCommSemiring.toOrderedSemiring.{u1} (WithTop.{u1} R) (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} (WithTop.{u1} R) (WithTop.instCanonicallyOrderedCommSemiringWithTop.{u1} R (fun (a : R) (b : R) => _inst_4 a b) _inst_3 _inst_5))))) (Semiring.toNonAssocSemiring.{u2} (WithTop.{u2} S) (OrderedSemiring.toSemiring.{u2} (WithTop.{u2} S) (OrderedCommSemiring.toOrderedSemiring.{u2} (WithTop.{u2} S) (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} (WithTop.{u2} S) (WithTop.instCanonicallyOrderedCommSemiringWithTop.{u2} S (fun (a : S) (b : S) => _inst_7 a b) _inst_6 _inst_8))))))
Case conversion may be inaccurate. Consider using '#align ring_hom.with_top_map WithTop.RingHom.withTopMapₓ'. -/
/-- A version of `with_top.map` for `ring_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def WithTop.RingHom.withTopMap {R S : Type _} [CanonicallyOrderedCommSemiring R]
    [DecidableEq R] [Nontrivial R] [CanonicallyOrderedCommSemiring S] [DecidableEq S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  { f.toMonoidWithZeroHom.WithTop.MonoidWithZeroHom.withTopMap hf, f.toAddMonoidHom.withTopMap with
    toFun := WithTop.map f }
#align ring_hom.with_top_map WithTop.RingHom.withTopMap

end WithTop

namespace WithBot

instance [Nonempty α] : Nontrivial (WithBot α) :=
  Option.nontrivial

variable [DecidableEq α]

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithBot α) :=
  WithTop.mulZeroClass

/- warning: with_bot.mul_def -> WithBot.mul_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithBot.{u1} α} {b : WithBot.{u1} α}, Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toHasMul.{u1} (WithBot.{u1} α) (WithBot.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) a b) (ite.{succ u1} (WithBot.{u1} α) (Or (Eq.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2))))) (Eq.{succ u1} (WithBot.{u1} α) b (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2)))))) (Or.decidable (Eq.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2))))) (Eq.{succ u1} (WithBot.{u1} α) b (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2))))) (Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2))))) (Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) b (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2)))))) (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2)))) (Option.map₂.{u1, u1, u1} α α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_3)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithBot.{u1} α} {b : WithBot.{u1} α}, Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toMul.{u1} (WithBot.{u1} α) (WithBot.instMulZeroClassWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) a b) (ite.{succ u1} (WithBot.{u1} α) (Or (Eq.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2)))) (Eq.{succ u1} (WithBot.{u1} α) b (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2))))) (instDecidableOr (Eq.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2)))) (Eq.{succ u1} (WithBot.{u1} α) b (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2)))) (WithBot.instDecidableEqWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2)))) (WithBot.instDecidableEqWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) b (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2))))) (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2))) (Option.map₂.{u1, u1, u1} α α α (fun (x._@.Mathlib.Algebra.Order.Ring.WithTop._hyg.2622 : α) (x._@.Mathlib.Algebra.Order.Ring.WithTop._hyg.2624 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_3) x._@.Mathlib.Algebra.Order.Ring.WithTop._hyg.2622 x._@.Mathlib.Algebra.Order.Ring.WithTop._hyg.2624) a b))
Case conversion may be inaccurate. Consider using '#align with_bot.mul_def WithBot.mul_defₓ'. -/
theorem mul_def {a b : WithBot α} : a * b = if a = 0 ∨ b = 0 then 0 else Option.map₂ (· * ·) a b :=
  rfl
#align with_bot.mul_def WithBot.mul_def

/- warning: with_bot.mul_bot -> WithBot.mul_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithBot.{u1} α}, (Ne.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2))))) -> (Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toHasMul.{u1} (WithBot.{u1} α) (WithBot.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) a (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithBot.{u1} α}, (Ne.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2)))) -> (Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toMul.{u1} (WithBot.{u1} α) (WithBot.instMulZeroClassWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) a (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)))
Case conversion may be inaccurate. Consider using '#align with_bot.mul_bot WithBot.mul_botₓ'. -/
@[simp]
theorem mul_bot {a : WithBot α} (h : a ≠ 0) : a * ⊥ = ⊥ :=
  WithTop.mul_top h
#align with_bot.mul_bot WithBot.mul_bot

/- warning: with_bot.bot_mul -> WithBot.bot_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithBot.{u1} α}, (Ne.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α _inst_2))))) -> (Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toHasMul.{u1} (WithBot.{u1} α) (WithBot.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α] {a : WithBot.{u1} α}, (Ne.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α _inst_2)))) -> (Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toMul.{u1} (WithBot.{u1} α) (WithBot.instMulZeroClassWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)) a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)))
Case conversion may be inaccurate. Consider using '#align with_bot.bot_mul WithBot.bot_mulₓ'. -/
@[simp]
theorem bot_mul {a : WithBot α} (h : a ≠ 0) : ⊥ * a = ⊥ :=
  WithTop.top_mul h
#align with_bot.bot_mul WithBot.bot_mul

/- warning: with_bot.bot_mul_bot -> WithBot.bot_mul_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α], Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toHasMul.{u1} (WithBot.{u1} α) (WithBot.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : Mul.{u1} α], Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toMul.{u1} (WithBot.{u1} α) (WithBot.instMulZeroClassWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))
Case conversion may be inaccurate. Consider using '#align with_bot.bot_mul_bot WithBot.bot_mul_botₓ'. -/
@[simp]
theorem bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ :=
  WithTop.top_mul_top
#align with_bot.bot_mul_bot WithBot.bot_mul_bot

end Mul

section MulZeroClass

variable [MulZeroClass α]

/- warning: with_bot.coe_mul -> WithBot.coe_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {a : α} {b : α}, Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) a b)) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toHasMul.{u1} (WithBot.{u1} α) (WithBot.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {a : α} {b : α}, Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) a b)) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toMul.{u1} (WithBot.{u1} α) (WithBot.instMulZeroClassWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) (WithBot.some.{u1} α a) (WithBot.some.{u1} α b))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_mul WithBot.coe_mulₓ'. -/
@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithBot α) = a * b :=
  WithTop.coe_mul
#align with_bot.coe_mul WithBot.coe_mul

/- warning: with_bot.mul_coe -> WithBot.mul_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {b : α}, (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))) -> (forall {a : WithBot.{u1} α}, Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toHasMul.{u1} (WithBot.{u1} α) (WithBot.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) b)) (Option.bind.{u1, u1} α α a (fun (a : α) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {b : α}, (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))) -> (forall {a : WithBot.{u1} α}, Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toMul.{u1} (WithBot.{u1} α) (WithBot.instMulZeroClassWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) a (WithBot.some.{u1} α b)) (Option.bind.{u1, u1} α α a (fun (a : α) => Option.some.{u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) a b))))
Case conversion may be inaccurate. Consider using '#align with_bot.mul_coe WithBot.mul_coeₓ'. -/
theorem mul_coe {b : α} (hb : b ≠ 0) {a : WithBot α} : a * b = a.bind fun a : α => ↑(a * b) :=
  WithTop.mul_coe hb
#align with_bot.mul_coe WithBot.mul_coe

/- warning: with_bot.mul_eq_bot_iff -> WithBot.mul_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {a : WithBot.{u1} α} {b : WithBot.{u1} α}, Iff (Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toHasMul.{u1} (WithBot.{u1} α) (WithBot.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) a b) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Or (And (Ne.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2)))))) (Eq.{succ u1} (WithBot.{u1} α) b (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) (And (Eq.{succ u1} (WithBot.{u1} α) a (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Ne.{succ u1} (WithBot.{u1} α) b (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (OfNat.mk.{u1} (WithBot.{u1} α) 0 (Zero.zero.{u1} (WithBot.{u1} α) (WithBot.hasZero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] {a : WithBot.{u1} α} {b : WithBot.{u1} α}, Iff (Eq.{succ u1} (WithBot.{u1} α) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toMul.{u1} (WithBot.{u1} α) (WithBot.instMulZeroClassWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) a b) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) (Or (And (Ne.{succ u1} (WithBot.{u1} α) a (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_2))))) (Eq.{succ u1} (WithBot.{u1} α) b (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)))) (And (Eq.{succ u1} (WithBot.{u1} α) a (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) (Ne.{succ u1} (WithBot.{u1} α) b (OfNat.ofNat.{u1} (WithBot.{u1} α) 0 (Zero.toOfNat0.{u1} (WithBot.{u1} α) (WithBot.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align with_bot.mul_eq_bot_iff WithBot.mul_eq_bot_iffₓ'. -/
@[simp]
theorem mul_eq_bot_iff {a b : WithBot α} : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff
#align with_bot.mul_eq_bot_iff WithBot.mul_eq_bot_iff

/- warning: with_bot.bot_lt_mul -> WithBot.bot_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] [_inst_3 : Preorder.{u1} α] {a : WithBot.{u1} α} {b : WithBot.{u1} α}, (LT.lt.{u1} (WithBot.{u1} α) (Preorder.toLT.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_3)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) a) -> (LT.lt.{u1} (WithBot.{u1} α) (Preorder.toLT.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_3)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) b) -> (LT.lt.{u1} (WithBot.{u1} α) (Preorder.toLT.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_3)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toHasMul.{u1} (WithBot.{u1} α) (WithBot.mulZeroClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α _inst_2) (MulZeroClass.toHasMul.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : MulZeroClass.{u1} α] [_inst_3 : Preorder.{u1} α] {a : WithBot.{u1} α} {b : WithBot.{u1} α}, (LT.lt.{u1} (WithBot.{u1} α) (Preorder.toLT.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_3)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)) a) -> (LT.lt.{u1} (WithBot.{u1} α) (Preorder.toLT.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_3)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)) b) -> (LT.lt.{u1} (WithBot.{u1} α) (Preorder.toLT.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_3)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)) (HMul.hMul.{u1, u1, u1} (WithBot.{u1} α) (WithBot.{u1} α) (WithBot.{u1} α) (instHMul.{u1} (WithBot.{u1} α) (MulZeroClass.toMul.{u1} (WithBot.{u1} α) (WithBot.instMulZeroClassWithBot.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toZero.{u1} α _inst_2) (MulZeroClass.toMul.{u1} α _inst_2)))) a b))
Case conversion may be inaccurate. Consider using '#align with_bot.bot_lt_mul WithBot.bot_lt_mulₓ'. -/
theorem bot_lt_mul [Preorder α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
  by
  lift a to α using ne_bot_of_gt ha
  lift b to α using ne_bot_of_gt hb
  simp only [← coe_mul, bot_lt_coe]
#align with_bot.bot_lt_mul WithBot.bot_lt_mul

end MulZeroClass

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithBot α) :=
  WithTop.mulZeroOneClass

instance [MulZeroClass α] [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
  WithTop.noZeroDivisors

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithBot α) :=
  WithTop.semigroupWithZero

instance [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZero (WithBot α) :=
  WithTop.monoidWithZero

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) :=
  WithTop.commMonoidWithZero

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : CommSemiring (WithBot α) :=
  WithTop.commSemiring

instance [MulZeroClass α] [Preorder α] [PosMulMono α] : PosMulMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
    rcases eq_or_ne x 0 with (rfl | x0'); · simp
    lift x to α;
    · rintro ⟨rfl⟩
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction a using WithBot.recBotCoe; · simp_rw [mul_bot x0', bot_le]
    induction b using WithBot.recBotCoe; · exact absurd h (bot_lt_coe a).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast  at x0
    exact mul_le_mul_of_nonneg_left h x0⟩

instance [MulZeroClass α] [Preorder α] [MulPosMono α] : MulPosMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
    rcases eq_or_ne x 0 with (rfl | x0'); · simp
    lift x to α;
    · rintro ⟨rfl⟩
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction a using WithBot.recBotCoe; · simp_rw [bot_mul x0', bot_le]
    induction b using WithBot.recBotCoe; · exact absurd h (bot_lt_coe a).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast  at x0
    exact mul_le_mul_of_nonneg_right h x0⟩

instance [MulZeroClass α] [Preorder α] [PosMulStrictMono α] : PosMulStrictMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
    lift x to α using x0.ne_bot
    induction b using WithBot.recBotCoe; · exact absurd h not_lt_bot
    induction a using WithBot.recBotCoe; · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast  at x0
    exact mul_lt_mul_of_pos_left h x0⟩

instance [MulZeroClass α] [Preorder α] [MulPosStrictMono α] : MulPosStrictMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
    lift x to α using x0.ne_bot
    induction b using WithBot.recBotCoe; · exact absurd h not_lt_bot
    induction a using WithBot.recBotCoe; · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast  at x0
    exact mul_lt_mul_of_pos_right h x0⟩

instance [MulZeroClass α] [Preorder α] [PosMulReflectLT α] : PosMulReflectLT (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk] at h
    rcases eq_or_ne x 0 with (rfl | x0'); · simpa using h
    lift x to α;
    · rintro ⟨rfl⟩
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction b using WithBot.recBotCoe;
    · rw [mul_bot x0'] at h
      exact absurd h bot_le.not_lt
    induction a using WithBot.recBotCoe; · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast  at x0
    exact lt_of_mul_lt_mul_left h x0⟩

instance [MulZeroClass α] [Preorder α] [MulPosReflectLT α] : MulPosReflectLT (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk] at h
    rcases eq_or_ne x 0 with (rfl | x0'); · simpa using h
    lift x to α;
    · rintro ⟨rfl⟩
      exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction b using WithBot.recBotCoe;
    · rw [bot_mul x0'] at h
      exact absurd h bot_le.not_lt
    induction a using WithBot.recBotCoe; · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast  at x0
    exact lt_of_mul_lt_mul_right h x0⟩

instance [MulZeroClass α] [Preorder α] [PosMulMonoRev α] : PosMulMonoRev (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk] at h
    lift x to α using x0.ne_bot
    induction a using WithBot.recBotCoe; · exact bot_le
    induction b using WithBot.recBotCoe
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe (x * a)).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast  at x0
    exact le_of_mul_le_mul_left h x0⟩

instance [MulZeroClass α] [Preorder α] [MulPosMonoRev α] : MulPosMonoRev (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk] at h
    lift x to α using x0.ne_bot
    induction a using WithBot.recBotCoe; · exact bot_le
    induction b using WithBot.recBotCoe
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe (a * x)).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast  at x0
    exact le_of_mul_le_mul_right h x0⟩

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : OrderedCommSemiring (WithBot α) :=
  { WithBot.zeroLeOneClass, WithBot.orderedAddCommMonoid,
    WithBot.commSemiring with
    mul_le_mul_of_nonneg_left := fun _ _ _ => mul_le_mul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun _ _ _ => mul_le_mul_of_nonneg_right }

end WithBot

