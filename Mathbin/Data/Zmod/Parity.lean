/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module data.zmod.parity
! leanprover-community/mathlib commit 290a7ba01fbcab1b64757bdaa270d28f4dcede35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Zmod.Basic

/-!
# Relating parity to natural numbers mod 2

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides lemmas relating `zmod 2` to `even` and `odd`.

## Tags

parity, zmod, even, odd
-/


namespace ZMod

/- warning: zmod.eq_zero_iff_even -> ZMod.eq_zero_iff_even is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Iff (Eq.{1} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Ring.toAddCommGroupWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (DivisionRing.toRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Field.toDivisionRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (ZMod.field (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) Nat.fact_prime_two)))))))))) n) (OfNat.ofNat.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (MulZeroClass.toHasZero.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NonUnitalNonAssocSemiring.toMulZeroClass.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Ring.toNonAssocRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (DivisionRing.toRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Field.toDivisionRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (ZMod.field (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Nat.fact_prime_two)))))))))))) (Even.{0} Nat Nat.hasAdd n)
but is expected to have type
  forall {n : Nat}, Iff (Eq.{1} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Nat.cast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (NonAssocRing.toNatCast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Ring.toNonAssocRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (DivisionRing.toRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Field.toDivisionRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (ZMod.instFieldZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Nat.fact_prime_two))))) n) (OfNat.ofNat.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Zero.toOfNat0.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (CommMonoidWithZero.toZero.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (CommGroupWithZero.toCommMonoidWithZero.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Semifield.toCommGroupWithZero.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Field.toSemifield.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (ZMod.instFieldZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Nat.fact_prime_two)))))))) (Even.{0} Nat instAddNat n)
Case conversion may be inaccurate. Consider using '#align zmod.eq_zero_iff_even ZMod.eq_zero_iff_evenₓ'. -/
theorem eq_zero_iff_even {n : ℕ} : (n : ZMod 2) = 0 ↔ Even n :=
  (CharP.cast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm
#align zmod.eq_zero_iff_even ZMod.eq_zero_iff_even

/- warning: zmod.eq_one_iff_odd -> ZMod.eq_one_iff_odd is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Iff (Eq.{1} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Ring.toAddCommGroupWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (DivisionRing.toRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Field.toDivisionRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (ZMod.field (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) Nat.fact_prime_two)))))))))) n) (OfNat.ofNat.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (AddMonoidWithOne.toOne.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Ring.toAddCommGroupWithOne.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (DivisionRing.toRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Field.toDivisionRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (ZMod.field (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Nat.fact_prime_two))))))))))) (Odd.{0} Nat Nat.semiring n)
but is expected to have type
  forall {n : Nat}, Iff (Eq.{1} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Nat.cast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (NonAssocRing.toNatCast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Ring.toNonAssocRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (DivisionRing.toRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Field.toDivisionRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (ZMod.instFieldZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Nat.fact_prime_two))))) n) (OfNat.ofNat.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (One.toOfNat1.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (NonAssocRing.toOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Ring.toNonAssocRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (DivisionRing.toRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Field.toDivisionRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (ZMod.instFieldZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Nat.fact_prime_two)))))))) (Odd.{0} Nat Nat.semiring n)
Case conversion may be inaccurate. Consider using '#align zmod.eq_one_iff_odd ZMod.eq_one_iff_oddₓ'. -/
theorem eq_one_iff_odd {n : ℕ} : (n : ZMod 2) = 1 ↔ Odd n :=
  by
  rw [← @Nat.cast_one (ZMod 2), ZMod.eq_iff_modEq_nat, Nat.odd_iff, Nat.ModEq]
  norm_num
#align zmod.eq_one_iff_odd ZMod.eq_one_iff_odd

/- warning: zmod.ne_zero_iff_odd -> ZMod.ne_zero_iff_odd is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Iff (Ne.{1} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Ring.toAddCommGroupWithOne.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (DivisionRing.toRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Field.toDivisionRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (ZMod.field (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) Nat.fact_prime_two)))))))))) n) (OfNat.ofNat.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (MulZeroClass.toHasZero.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NonUnitalNonAssocSemiring.toMulZeroClass.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Ring.toNonAssocRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (DivisionRing.toRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Field.toDivisionRing.{0} (ZMod (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (ZMod.field (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Nat.fact_prime_two)))))))))))) (Odd.{0} Nat Nat.semiring n)
but is expected to have type
  forall {n : Nat}, Iff (Ne.{1} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Nat.cast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (NonAssocRing.toNatCast.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Ring.toNonAssocRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (DivisionRing.toRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Field.toDivisionRing.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (ZMod.instFieldZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Nat.fact_prime_two))))) n) (OfNat.ofNat.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Zero.toOfNat0.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (CommMonoidWithZero.toZero.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (CommGroupWithZero.toCommMonoidWithZero.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Semifield.toCommGroupWithZero.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Field.toSemifield.{0} (ZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (ZMod.instFieldZMod (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) Nat.fact_prime_two)))))))) (Odd.{0} Nat Nat.semiring n)
Case conversion may be inaccurate. Consider using '#align zmod.ne_zero_iff_odd ZMod.ne_zero_iff_oddₓ'. -/
theorem ne_zero_iff_odd {n : ℕ} : (n : ZMod 2) ≠ 0 ↔ Odd n := by
  constructor <;>
    · contrapose
      simp [eq_zero_iff_even]
#align zmod.ne_zero_iff_odd ZMod.ne_zero_iff_odd

end ZMod

