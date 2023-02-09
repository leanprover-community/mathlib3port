/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.group_action.sub_mul_action.pointwise
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.SubMulAction

/-!
# Pointwise monoid structures on sub_mul_action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides `sub_mul_action.monoid` and weaker typeclasses, which show that `sub_mul_action`s
inherit the same pointwise multiplications as sets.

To match `submodule.semiring`, we do not put these in the `pointwise` locale.

-/


open Pointwise

variable {R M : Type _}

namespace SubMulAction

section One

variable [Monoid R] [MulAction R M] [One M]

instance : One (SubMulAction R M)
    where one :=
    { carrier := Set.range fun r : R => r • (1 : M)
      smul_mem' := fun r m ⟨r', hr'⟩ => hr' ▸ ⟨r * r', mul_smul _ _ _⟩ }

#print SubMulAction.coe_one /-
theorem coe_one : ↑(1 : SubMulAction R M) = Set.range fun r : R => r • (1 : M) :=
  rfl
#align sub_mul_action.coe_one SubMulAction.coe_one
-/

#print SubMulAction.mem_one /-
@[simp]
theorem mem_one {x : M} : x ∈ (1 : SubMulAction R M) ↔ ∃ r : R, r • 1 = x :=
  Iff.rfl
#align sub_mul_action.mem_one SubMulAction.mem_one
-/

#print SubMulAction.subset_coe_one /-
theorem subset_coe_one : (1 : Set M) ⊆ (1 : SubMulAction R M) := fun x hx =>
  ⟨1, (one_smul _ _).trans hx.symm⟩
#align sub_mul_action.subset_coe_one SubMulAction.subset_coe_one
-/

end One

section Mul

variable [Monoid R] [MulAction R M] [Mul M] [IsScalarTower R M M]

instance : Mul (SubMulAction R M)
    where mul p q :=
    { carrier := Set.image2 (· * ·) p q
      smul_mem' := fun r m ⟨m₁, m₂, hm₁, hm₂, h⟩ =>
        h ▸ smul_mul_assoc r m₁ m₂ ▸ Set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ }

/- warning: sub_mul_action.coe_mul -> SubMulAction.coe_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1] [_inst_3 : Mul.{u2} M] [_inst_4 : IsScalarTower.{u1, u2, u2} R M M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (Mul.toSMul.{u2} M _inst_3) (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)] (p : SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (q : SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)), Eq.{succ u2} (Set.{u2} M) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))))) (HMul.hMul.{u2, u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (instHMul.{u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SubMulAction.hasMul.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4)) p q)) (HMul.hMul.{u2, u2, u2} (Set.{u2} M) (Set.{u2} M) (Set.{u2} M) (instHMul.{u2} (Set.{u2} M) (Set.mul.{u2} M _inst_3)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))))) p) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))))) q))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1] [_inst_3 : Mul.{u1} M] [_inst_4 : IsScalarTower.{u2, u1, u1} R M M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (Mul.toSMul.{u1} M _inst_3) (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)] (p : SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (q : SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)), Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (instHMul.{u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SubMulAction.instMulSubMulActionToSMul.{u2, u1} R M _inst_1 _inst_2 _inst_3 _inst_4)) p q)) (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M _inst_3)) (SetLike.coe.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) p) (SetLike.coe.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) q))
Case conversion may be inaccurate. Consider using '#align sub_mul_action.coe_mul SubMulAction.coe_mulₓ'. -/
@[norm_cast]
theorem coe_mul (p q : SubMulAction R M) : ↑(p * q) = (p * q : Set M) :=
  rfl
#align sub_mul_action.coe_mul SubMulAction.coe_mul

/- warning: sub_mul_action.mem_mul -> SubMulAction.mem_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1] [_inst_3 : Mul.{u2} M] [_inst_4 : IsScalarTower.{u1, u2, u2} R M M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (Mul.toSMul.{u2} M _inst_3) (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)] {p : SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)} {q : SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)} {x : M}, Iff (Membership.Mem.{u2, u2} M (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SetLike.hasMem.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))) x (HMul.hMul.{u2, u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (instHMul.{u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SubMulAction.hasMul.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4)) p q)) (Exists.{succ u2} M (fun (y : M) => Exists.{succ u2} M (fun (z : M) => And (Membership.Mem.{u2, u2} M (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SetLike.hasMem.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))) y p) (And (Membership.Mem.{u2, u2} M (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SetLike.hasMem.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))) z q) (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) y z) x)))))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1] [_inst_3 : Mul.{u1} M] [_inst_4 : IsScalarTower.{u2, u1, u1} R M M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (Mul.toSMul.{u1} M _inst_3) (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)] {p : SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)} {q : SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)} {x : M}, Iff (Membership.mem.{u1, u1} M (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SetLike.instMembership.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2))) x (HMul.hMul.{u1, u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (instHMul.{u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SubMulAction.instMulSubMulActionToSMul.{u2, u1} R M _inst_1 _inst_2 _inst_3 _inst_4)) p q)) (Exists.{succ u1} M (fun (y : M) => Exists.{succ u1} M (fun (z : M) => And (Membership.mem.{u1, u1} M (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SetLike.instMembership.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2))) y p) (And (Membership.mem.{u1, u1} M (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SetLike.instMembership.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2))) z q) (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) y z) x)))))
Case conversion may be inaccurate. Consider using '#align sub_mul_action.mem_mul SubMulAction.mem_mulₓ'. -/
theorem mem_mul {p q : SubMulAction R M} {x : M} : x ∈ p * q ↔ ∃ y z, y ∈ p ∧ z ∈ q ∧ y * z = x :=
  Set.mem_mul
#align sub_mul_action.mem_mul SubMulAction.mem_mul

end Mul

section MulOneClass

variable [Monoid R] [MulAction R M] [MulOneClass M] [IsScalarTower R M M] [SMulCommClass R M M]

instance : MulOneClass (SubMulAction R M)
    where
  mul := (· * ·)
  one := 1
  mul_one a := by
    ext
    simp only [mem_mul, mem_one, mul_smul_comm, exists_and_left, exists_exists_eq_and, mul_one]
    constructor
    · rintro ⟨y, hy, r, rfl⟩
      exact smul_mem _ _ hy
    · intro hx
      exact ⟨x, hx, 1, one_smul _ _⟩
  one_mul a := by
    ext
    simp only [mem_mul, mem_one, smul_mul_assoc, exists_and_left, exists_exists_eq_and, one_mul]
    refine' ⟨_, fun hx => ⟨1, x, hx, one_smul _ _⟩⟩
    rintro ⟨r, y, hy, rfl⟩
    exact smul_mem _ _ hy

end MulOneClass

section Semigroup

variable [Monoid R] [MulAction R M] [Semigroup M] [IsScalarTower R M M]

instance : Semigroup (SubMulAction R M)
    where
  mul := (· * ·)
  mul_assoc a b c := SetLike.coe_injective (mul_assoc (_ : Set _) _ _)

end Semigroup

section Monoid

variable [Monoid R] [MulAction R M] [Monoid M] [IsScalarTower R M M] [SMulCommClass R M M]

instance : Monoid (SubMulAction R M) :=
  { SubMulAction.semigroup,
    SubMulAction.mulOneClass with
    mul := (· * ·)
    one := 1 }

/- warning: sub_mul_action.coe_pow -> SubMulAction.coe_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1] [_inst_3 : Monoid.{u2} M] [_inst_4 : IsScalarTower.{u1, u2, u2} R M M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3))) (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)] [_inst_5 : SMulCommClass.{u1, u2, u2} R M M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3)))] (p : SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u2} (Set.{u2} M) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))))) (HPow.hPow.{u2, 0, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) Nat (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (instHPow.{u2, 0} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) Nat (Monoid.Pow.{u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SubMulAction.monoid.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) p n)) (HPow.hPow.{u2, 0, u2} (Set.{u2} M) Nat (Set.{u2} M) (instHPow.{u2, 0} (Set.{u2} M) Nat (Set.NPow.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3)) (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3)))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))))) p) n))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1] [_inst_3 : Monoid.{u1} M] [_inst_4 : IsScalarTower.{u2, u1, u1} R M M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (MulAction.toSMul.{u1, u1} M M _inst_3 (Monoid.toMulAction.{u1} M _inst_3)) (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)] [_inst_5 : SMulCommClass.{u2, u1, u1} R M M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (MulAction.toSMul.{u1, u1} M M _inst_3 (Monoid.toMulAction.{u1} M _inst_3))] (p : SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (HPow.hPow.{u1, 0, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) Nat (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (instHPow.{u1, 0} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) Nat (Monoid.Pow.{u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SubMulAction.instMonoidSubMulActionToSMul.{u2, u1} R M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) p n)) (HPow.hPow.{u1, 0, u1} (Set.{u1} M) Nat (Set.{u1} M) (instHPow.{u1, 0} (Set.{u1} M) Nat (Set.NPow.{u1} M (Monoid.toOne.{u1} M _inst_3) (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) (SetLike.coe.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) p) n))
Case conversion may be inaccurate. Consider using '#align sub_mul_action.coe_pow SubMulAction.coe_powₓ'. -/
theorem coe_pow (p : SubMulAction R M) : ∀ {n : ℕ} (hn : n ≠ 0), ↑(p ^ n) = (p ^ n : Set M)
  | 0, hn => (hn rfl).elim
  | 1, hn => by rw [pow_one, pow_one]
  | n + 2, hn => by rw [pow_succ _ (n + 1), pow_succ _ (n + 1), coe_mul, coe_pow n.succ_ne_zero]
#align sub_mul_action.coe_pow SubMulAction.coe_pow

/- warning: sub_mul_action.subset_coe_pow -> SubMulAction.subset_coe_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Monoid.{u1} R] [_inst_2 : MulAction.{u1, u2} R M _inst_1] [_inst_3 : Monoid.{u2} M] [_inst_4 : IsScalarTower.{u1, u2, u2} R M M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3))) (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)] [_inst_5 : SMulCommClass.{u1, u2, u2} R M M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2) (Mul.toSMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3)))] (p : SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) {n : Nat}, HasSubset.Subset.{u2} (Set.{u2} M) (Set.hasSubset.{u2} M) (HPow.hPow.{u2, 0, u2} (Set.{u2} M) Nat (Set.{u2} M) (instHPow.{u2, 0} (Set.{u2} M) Nat (Set.NPow.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3)) (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3)))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))))) p) n) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) M (SubMulAction.setLike.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2))))) (HPow.hPow.{u2, 0, u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) Nat (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (instHPow.{u2, 0} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) Nat (Monoid.Pow.{u2} (SubMulAction.{u1, u2} R M (MulAction.toHasSmul.{u1, u2} R M _inst_1 _inst_2)) (SubMulAction.monoid.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) p n))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Monoid.{u2} R] [_inst_2 : MulAction.{u2, u1} R M _inst_1] [_inst_3 : Monoid.{u1} M] [_inst_4 : IsScalarTower.{u2, u1, u1} R M M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (MulAction.toSMul.{u1, u1} M M _inst_3 (Monoid.toMulAction.{u1} M _inst_3)) (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)] [_inst_5 : SMulCommClass.{u2, u1, u1} R M M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2) (MulAction.toSMul.{u1, u1} M M _inst_3 (Monoid.toMulAction.{u1} M _inst_3))] (p : SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) {n : Nat}, HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) (HPow.hPow.{u1, 0, u1} (Set.{u1} M) Nat (Set.{u1} M) (instHPow.{u1, 0} (Set.{u1} M) Nat (Set.NPow.{u1} M (Monoid.toOne.{u1} M _inst_3) (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) (SetLike.coe.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) p) n) (SetLike.coe.{u1, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) M (SubMulAction.instSetLikeSubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (HPow.hPow.{u1, 0, u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) Nat (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (instHPow.{u1, 0} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) Nat (Monoid.Pow.{u1} (SubMulAction.{u2, u1} R M (MulAction.toSMul.{u2, u1} R M _inst_1 _inst_2)) (SubMulAction.instMonoidSubMulActionToSMul.{u2, u1} R M _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) p n))
Case conversion may be inaccurate. Consider using '#align sub_mul_action.subset_coe_pow SubMulAction.subset_coe_powₓ'. -/
theorem subset_coe_pow (p : SubMulAction R M) : ∀ {n : ℕ}, (p ^ n : Set M) ⊆ ↑(p ^ n)
  | 0 => by
    rw [pow_zero, pow_zero]
    exact subset_coe_one
  | n + 1 => (coe_pow p n.succ_ne_zero).Superset
#align sub_mul_action.subset_coe_pow SubMulAction.subset_coe_pow

end Monoid

end SubMulAction

