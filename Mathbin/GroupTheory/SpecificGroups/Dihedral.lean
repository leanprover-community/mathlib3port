/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam

! This file was ported from Lean 3 source module group_theory.specific_groups.dihedral
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.Exponent

/-!
# Dihedral Groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the dihedral groups `dihedral_group n`, with elements `r i` and `sr i` for `i : zmod n`.

For `n ≠ 0`, `dihedral_group n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `dihedral_group 0` corresponds to the infinite dihedral group.
-/


#print DihedralGroup /-
/-- For `n ≠ 0`, `dihedral_group n` represents the symmetry group of the regular `n`-gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of
the `n`-gon. `dihedral_group 0` corresponds to the infinite dihedral group.
-/
inductive DihedralGroup (n : ℕ) : Type
  | r : ZMod n → DihedralGroup
  | sr : ZMod n → DihedralGroup
  deriving DecidableEq
#align dihedral_group DihedralGroup
-/

namespace DihedralGroup

variable {n : ℕ}

/-- Multiplication of the dihedral group.
-/
private def mul : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

/-- The identity `1` is the rotation by `0`.
-/
private def one : DihedralGroup n :=
  r 0

instance : Inhabited (DihedralGroup n) :=
  ⟨one⟩

/-- The inverse of a an element of the dihedral group.
-/
private def inv : DihedralGroup n → DihedralGroup n
  | r i => r (-i)
  | sr i => sr i

/-- The group structure on `dihedral_group n`.
-/
instance : Group (DihedralGroup n) where
  mul := mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [mul] <;> ring
  one := one
  one_mul := by
    rintro (a | a)
    exact congr_arg r (zero_add a)
    exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    exact congr_arg r (add_zero a)
    exact congr_arg sr (add_zero a)
  inv := inv
  mul_left_inv := by
    rintro (a | a)
    exact congr_arg r (neg_add_self a)
    exact congr_arg r (sub_self a)

/- warning: dihedral_group.r_mul_r -> DihedralGroup.r_mul_r is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (i : ZMod n) (j : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toHasMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n)))))) (DihedralGroup.r n i) (DihedralGroup.r n j)) (DihedralGroup.r n (HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n) (instHAdd.{0} (ZMod n) (Distrib.toHasAdd.{0} (ZMod n) (Ring.toDistrib.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))) i j))
but is expected to have type
  forall {n : Nat} (i : ZMod n) (j : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n)))))) (DihedralGroup.r n i) (DihedralGroup.r n j)) (DihedralGroup.r n (HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n) (instHAdd.{0} (ZMod n) (Distrib.toAdd.{0} (ZMod n) (NonUnitalNonAssocSemiring.toDistrib.{0} (ZMod n) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod n) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod n) (Ring.toNonAssocRing.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))) i j))
Case conversion may be inaccurate. Consider using '#align dihedral_group.r_mul_r DihedralGroup.r_mul_rₓ'. -/
@[simp]
theorem r_mul_r (i j : ZMod n) : r i * r j = r (i + j) :=
  rfl
#align dihedral_group.r_mul_r DihedralGroup.r_mul_r

/- warning: dihedral_group.r_mul_sr -> DihedralGroup.r_mul_sr is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (i : ZMod n) (j : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toHasMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n)))))) (DihedralGroup.r n i) (DihedralGroup.sr n j)) (DihedralGroup.sr n (HSub.hSub.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n) (instHSub.{0} (ZMod n) (SubNegMonoid.toHasSub.{0} (ZMod n) (AddGroup.toSubNegMonoid.{0} (ZMod n) (AddGroupWithOne.toAddGroup.{0} (ZMod n) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod n) (Ring.toAddCommGroupWithOne.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))) j i))
but is expected to have type
  forall {n : Nat} (i : ZMod n) (j : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n)))))) (DihedralGroup.r n i) (DihedralGroup.sr n j)) (DihedralGroup.sr n (HSub.hSub.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n) (instHSub.{0} (ZMod n) (Ring.toSub.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))) j i))
Case conversion may be inaccurate. Consider using '#align dihedral_group.r_mul_sr DihedralGroup.r_mul_srₓ'. -/
@[simp]
theorem r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i) :=
  rfl
#align dihedral_group.r_mul_sr DihedralGroup.r_mul_sr

/- warning: dihedral_group.sr_mul_r -> DihedralGroup.sr_mul_r is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (i : ZMod n) (j : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toHasMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n)))))) (DihedralGroup.sr n i) (DihedralGroup.r n j)) (DihedralGroup.sr n (HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n) (instHAdd.{0} (ZMod n) (Distrib.toHasAdd.{0} (ZMod n) (Ring.toDistrib.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))) i j))
but is expected to have type
  forall {n : Nat} (i : ZMod n) (j : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n)))))) (DihedralGroup.sr n i) (DihedralGroup.r n j)) (DihedralGroup.sr n (HAdd.hAdd.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n) (instHAdd.{0} (ZMod n) (Distrib.toAdd.{0} (ZMod n) (NonUnitalNonAssocSemiring.toDistrib.{0} (ZMod n) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod n) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod n) (Ring.toNonAssocRing.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))) i j))
Case conversion may be inaccurate. Consider using '#align dihedral_group.sr_mul_r DihedralGroup.sr_mul_rₓ'. -/
@[simp]
theorem sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j) :=
  rfl
#align dihedral_group.sr_mul_r DihedralGroup.sr_mul_r

/- warning: dihedral_group.sr_mul_sr -> DihedralGroup.sr_mul_sr is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (i : ZMod n) (j : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toHasMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n)))))) (DihedralGroup.sr n i) (DihedralGroup.sr n j)) (DihedralGroup.r n (HSub.hSub.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n) (instHSub.{0} (ZMod n) (SubNegMonoid.toHasSub.{0} (ZMod n) (AddGroup.toSubNegMonoid.{0} (ZMod n) (AddGroupWithOne.toAddGroup.{0} (ZMod n) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod n) (Ring.toAddCommGroupWithOne.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))) j i))
but is expected to have type
  forall {n : Nat} (i : ZMod n) (j : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n)))))) (DihedralGroup.sr n i) (DihedralGroup.sr n j)) (DihedralGroup.r n (HSub.hSub.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n) (instHSub.{0} (ZMod n) (Ring.toSub.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))) j i))
Case conversion may be inaccurate. Consider using '#align dihedral_group.sr_mul_sr DihedralGroup.sr_mul_srₓ'. -/
@[simp]
theorem sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i) :=
  rfl
#align dihedral_group.sr_mul_sr DihedralGroup.sr_mul_sr

/- warning: dihedral_group.one_def -> DihedralGroup.one_def is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} (DihedralGroup n) (OfNat.ofNat.{0} (DihedralGroup n) 1 (OfNat.mk.{0} (DihedralGroup n) 1 (One.one.{0} (DihedralGroup n) (MulOneClass.toHasOne.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n)))))))) (DihedralGroup.r n (OfNat.ofNat.{0} (ZMod n) 0 (OfNat.mk.{0} (ZMod n) 0 (Zero.zero.{0} (ZMod n) (MulZeroClass.toHasZero.{0} (ZMod n) (NonUnitalNonAssocSemiring.toMulZeroClass.{0} (ZMod n) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod n) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod n) (Ring.toNonAssocRing.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))))))
but is expected to have type
  forall {n : Nat}, Eq.{1} (DihedralGroup n) (OfNat.ofNat.{0} (DihedralGroup n) 1 (One.toOfNat1.{0} (DihedralGroup n) (InvOneClass.toOne.{0} (DihedralGroup n) (DivInvOneMonoid.toInvOneClass.{0} (DihedralGroup n) (DivisionMonoid.toDivInvOneMonoid.{0} (DihedralGroup n) (Group.toDivisionMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n))))))) (DihedralGroup.r n (OfNat.ofNat.{0} (ZMod n) 0 (Zero.toOfNat0.{0} (ZMod n) (CommMonoidWithZero.toZero.{0} (ZMod n) (CommSemiring.toCommMonoidWithZero.{0} (ZMod n) (CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))
Case conversion may be inaccurate. Consider using '#align dihedral_group.one_def DihedralGroup.one_defₓ'. -/
theorem one_def : (1 : DihedralGroup n) = r 0 :=
  rfl
#align dihedral_group.one_def DihedralGroup.one_def

private def fintype_helper : Sum (ZMod n) (ZMod n) ≃ DihedralGroup n
    where
  invFun i :=
    match i with
    | r j => Sum.inl j
    | sr j => Sum.inr j
  toFun i :=
    match i with
    | Sum.inl j => r j
    | Sum.inr j => sr j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- If `0 < n`, then `dihedral_group n` is a finite group.
-/
instance [NeZero n] : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

instance : Nontrivial (DihedralGroup n) :=
  ⟨⟨r 0, sr 0, by decide⟩⟩

#print DihedralGroup.card /-
/-- If `0 < n`, then `dihedral_group n` has `2n` elements.
-/
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← fintype.card_eq.mpr ⟨fintype_helper⟩, Fintype.card_sum, ZMod.card, two_mul]
#align dihedral_group.card DihedralGroup.card
-/

/- warning: dihedral_group.r_one_pow -> DihedralGroup.r_one_pow is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (k : Nat), Eq.{1} (DihedralGroup n) (HPow.hPow.{0, 0, 0} (DihedralGroup n) Nat (DihedralGroup n) (instHPow.{0, 0} (DihedralGroup n) Nat (Monoid.Pow.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n))))) (DihedralGroup.r n (OfNat.ofNat.{0} (ZMod n) 1 (OfNat.mk.{0} (ZMod n) 1 (One.one.{0} (ZMod n) (AddMonoidWithOne.toOne.{0} (ZMod n) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod n) (Ring.toAddCommGroupWithOne.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))))) k) (DihedralGroup.r n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (ZMod n) (HasLiftT.mk.{1, 1} Nat (ZMod n) (CoeTCₓ.coe.{1, 1} Nat (ZMod n) (Nat.castCoe.{0} (ZMod n) (AddMonoidWithOne.toNatCast.{0} (ZMod n) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod n) (Ring.toAddCommGroupWithOne.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))))))) k))
but is expected to have type
  forall {n : Nat} (k : Nat), Eq.{1} (DihedralGroup n) (HPow.hPow.{0, 0, 0} (DihedralGroup n) Nat (DihedralGroup n) (instHPow.{0, 0} (DihedralGroup n) Nat (Monoid.Pow.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n))))) (DihedralGroup.r n (OfNat.ofNat.{0} (ZMod n) 1 (One.toOfNat1.{0} (ZMod n) (Semiring.toOne.{0} (ZMod n) (CommSemiring.toSemiring.{0} (ZMod n) (CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))) k) (DihedralGroup.r n (Nat.cast.{0} (ZMod n) (Semiring.toNatCast.{0} (ZMod n) (CommSemiring.toSemiring.{0} (ZMod n) (CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))) k))
Case conversion may be inaccurate. Consider using '#align dihedral_group.r_one_pow DihedralGroup.r_one_powₓ'. -/
@[simp]
theorem r_one_pow (k : ℕ) : (r 1 : DihedralGroup n) ^ k = r k :=
  by
  induction' k with k IH
  · rw [Nat.cast_zero]; rfl
  · rw [pow_succ, IH, r_mul_r]
    congr 1
    norm_cast
    rw [Nat.one_add]
#align dihedral_group.r_one_pow DihedralGroup.r_one_pow

/- warning: dihedral_group.r_one_pow_n -> DihedralGroup.r_one_pow_n is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} (DihedralGroup n) (HPow.hPow.{0, 0, 0} (DihedralGroup n) Nat (DihedralGroup n) (instHPow.{0, 0} (DihedralGroup n) Nat (Monoid.Pow.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n))))) (DihedralGroup.r n (OfNat.ofNat.{0} (ZMod n) 1 (OfNat.mk.{0} (ZMod n) 1 (One.one.{0} (ZMod n) (AddMonoidWithOne.toOne.{0} (ZMod n) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod n) (Ring.toAddCommGroupWithOne.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))))) n) (OfNat.ofNat.{0} (DihedralGroup n) 1 (OfNat.mk.{0} (DihedralGroup n) 1 (One.one.{0} (DihedralGroup n) (MulOneClass.toHasOne.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n))))))))
but is expected to have type
  forall {n : Nat}, Eq.{1} (DihedralGroup n) (HPow.hPow.{0, 0, 0} (DihedralGroup n) Nat (DihedralGroup n) (instHPow.{0, 0} (DihedralGroup n) Nat (Monoid.Pow.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n))))) (DihedralGroup.r n (OfNat.ofNat.{0} (ZMod n) 1 (One.toOfNat1.{0} (ZMod n) (Semiring.toOne.{0} (ZMod n) (CommSemiring.toSemiring.{0} (ZMod n) (CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))) n) (OfNat.ofNat.{0} (DihedralGroup n) 1 (One.toOfNat1.{0} (DihedralGroup n) (InvOneClass.toOne.{0} (DihedralGroup n) (DivInvOneMonoid.toInvOneClass.{0} (DihedralGroup n) (DivisionMonoid.toDivInvOneMonoid.{0} (DihedralGroup n) (Group.toDivisionMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n)))))))
Case conversion may be inaccurate. Consider using '#align dihedral_group.r_one_pow_n DihedralGroup.r_one_pow_nₓ'. -/
@[simp]
theorem r_one_pow_n : r (1 : ZMod n) ^ n = 1 :=
  by
  rw [r_one_pow, one_def]
  congr 1
  exact ZMod.nat_cast_self _
#align dihedral_group.r_one_pow_n DihedralGroup.r_one_pow_n

/- warning: dihedral_group.sr_mul_self -> DihedralGroup.sr_mul_self is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (i : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toHasMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n)))))) (DihedralGroup.sr n i) (DihedralGroup.sr n i)) (OfNat.ofNat.{0} (DihedralGroup n) 1 (OfNat.mk.{0} (DihedralGroup n) 1 (One.one.{0} (DihedralGroup n) (MulOneClass.toHasOne.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n))))))))
but is expected to have type
  forall {n : Nat} (i : ZMod n), Eq.{1} (DihedralGroup n) (HMul.hMul.{0, 0, 0} (DihedralGroup n) (DihedralGroup n) (DihedralGroup n) (instHMul.{0} (DihedralGroup n) (MulOneClass.toMul.{0} (DihedralGroup n) (Monoid.toMulOneClass.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n)))))) (DihedralGroup.sr n i) (DihedralGroup.sr n i)) (OfNat.ofNat.{0} (DihedralGroup n) 1 (One.toOfNat1.{0} (DihedralGroup n) (InvOneClass.toOne.{0} (DihedralGroup n) (DivInvOneMonoid.toInvOneClass.{0} (DihedralGroup n) (DivisionMonoid.toDivInvOneMonoid.{0} (DihedralGroup n) (Group.toDivisionMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n)))))))
Case conversion may be inaccurate. Consider using '#align dihedral_group.sr_mul_self DihedralGroup.sr_mul_selfₓ'. -/
@[simp]
theorem sr_mul_self (i : ZMod n) : sr i * sr i = 1 := by rw [sr_mul_sr, sub_self, one_def]
#align dihedral_group.sr_mul_self DihedralGroup.sr_mul_self

/- warning: dihedral_group.order_of_sr -> DihedralGroup.orderOf_sr is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (i : ZMod n), Eq.{1} Nat (orderOf.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n))) (DihedralGroup.sr n i)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {n : Nat} (i : ZMod n), Eq.{1} Nat (orderOf.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n))) (DihedralGroup.sr n i)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
Case conversion may be inaccurate. Consider using '#align dihedral_group.order_of_sr DihedralGroup.orderOf_srₓ'. -/
/-- If `0 < n`, then `sr i` has order 2.
-/
@[simp]
theorem orderOf_sr (i : ZMod n) : orderOf (sr i) = 2 :=
  by
  rw [orderOf_eq_prime _ _]
  · exact ⟨Nat.prime_two⟩
  rw [sq, sr_mul_self]
  decide
#align dihedral_group.order_of_sr DihedralGroup.orderOf_sr

/- warning: dihedral_group.order_of_r_one -> DihedralGroup.orderOf_r_one is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} Nat (orderOf.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n))) (DihedralGroup.r n (OfNat.ofNat.{0} (ZMod n) 1 (OfNat.mk.{0} (ZMod n) 1 (One.one.{0} (ZMod n) (AddMonoidWithOne.toOne.{0} (ZMod n) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod n) (Ring.toAddCommGroupWithOne.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))))))))) n
but is expected to have type
  forall {n : Nat}, Eq.{1} Nat (orderOf.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n))) (DihedralGroup.r n (OfNat.ofNat.{0} (ZMod n) 1 (One.toOfNat1.{0} (ZMod n) (Semiring.toOne.{0} (ZMod n) (CommSemiring.toSemiring.{0} (ZMod n) (CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))))) n
Case conversion may be inaccurate. Consider using '#align dihedral_group.order_of_r_one DihedralGroup.orderOf_r_oneₓ'. -/
/-- If `0 < n`, then `r 1` has order `n`.
-/
@[simp]
theorem orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n :=
  by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · rw [orderOf_eq_zero_iff']
    intro n hn
    rw [r_one_pow, one_def]
    apply mt r.inj
    simpa using hn.ne'
  · skip
    apply
      (Nat.le_of_dvd (NeZero.pos n) <|
            orderOf_dvd_of_pow_eq_one <| @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← ZMod.val_eq_zero, ZMod.val_nat_cast, Nat.mod_eq_of_lt h] at h2
    exact absurd h2.symm (orderOf_pos _).Ne
#align dihedral_group.order_of_r_one DihedralGroup.orderOf_r_one

/- warning: dihedral_group.order_of_r -> DihedralGroup.orderOf_r is a dubious translation:
lean 3 declaration is
  forall {n : Nat} [_inst_1 : NeZero.{0} Nat Nat.hasZero n] (i : ZMod n), Eq.{1} Nat (orderOf.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n))) (DihedralGroup.r n i)) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) n (Nat.gcd n (ZMod.val n i)))
but is expected to have type
  forall {n : Nat} [_inst_1 : NeZero.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) n] (i : ZMod n), Eq.{1} Nat (orderOf.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n))) (DihedralGroup.r n i)) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) n (Nat.gcd n (ZMod.val n i)))
Case conversion may be inaccurate. Consider using '#align dihedral_group.order_of_r DihedralGroup.orderOf_rₓ'. -/
/-- If `0 < n`, then `i : zmod n` has order `n / gcd n i`.
-/
theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val :=
  by
  conv_lhs => rw [← ZMod.nat_cast_zmod_val i]
  rw [← r_one_pow, orderOf_pow, order_of_r_one]
#align dihedral_group.order_of_r DihedralGroup.orderOf_r

/- warning: dihedral_group.exponent -> DihedralGroup.exponent is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} Nat (Monoid.exponent.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.group n)))) (GCDMonoid.lcm.{0} Nat Nat.cancelCommMonoidWithZero Nat.gcdMonoid n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {n : Nat}, Eq.{1} Nat (Monoid.exponent.{0} (DihedralGroup n) (DivInvMonoid.toMonoid.{0} (DihedralGroup n) (Group.toDivInvMonoid.{0} (DihedralGroup n) (DihedralGroup.instGroupDihedralGroup n)))) (GCDMonoid.lcm.{0} Nat Nat.cancelCommMonoidWithZero instGCDMonoidNatCancelCommMonoidWithZero n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align dihedral_group.exponent DihedralGroup.exponentₓ'. -/
theorem exponent : Monoid.exponent (DihedralGroup n) = lcm n 2 :=
  by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · exact Monoid.exponent_eq_zero_of_order_zero order_of_r_one
  skip
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, order_of_r]
      refine' Nat.dvd_trans ⟨gcd n m.val, _⟩ (dvd_lcm_left n 2)
      · exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, order_of_sr]
      exact dvd_lcm_right n 2
  · apply lcm_dvd
    · convert Monoid.order_dvd_exponent (r 1)
      exact order_of_r_one.symm
    · convert Monoid.order_dvd_exponent (sr 0)
      exact (order_of_sr 0).symm
#align dihedral_group.exponent DihedralGroup.exponent

end DihedralGroup

