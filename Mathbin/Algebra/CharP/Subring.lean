/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.char_p.subring
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.RingTheory.Subring.Basic

/-!
# Characteristic of subrings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v

namespace CharP

/- warning: char_p.subsemiring -> CharP.subsemiring is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] (p : Nat) [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) p] (S : Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)), CharP.{u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Subsemiring.setLike.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) S) (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Subsemiring.setLike.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) S) (NonAssocSemiring.toAddCommMonoidWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Subsemiring.setLike.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) S) (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1) S))) p
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] (p : Nat) [_inst_2 : CharP.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) p] (S : Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)), CharP.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Subsemiring.instSetLikeSubsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) x S)) (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Subsemiring.instSetLikeSubsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) x S)) (NonAssocSemiring.toAddCommMonoidWithOne.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Subsemiring.instSetLikeSubsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) x S)) (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1) S))) p
Case conversion may be inaccurate. Consider using '#align char_p.subsemiring CharP.subsemiringₓ'. -/
instance subsemiring (R : Type u) [Semiring R] (p : ℕ) [CharP R p] (S : Subsemiring R) :
    CharP S p :=
  ⟨fun x =>
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h => Subtype.eq <| show S.Subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.Subtype x ▸ by rw [h, RingHom.map_zero]⟩⟩
#align char_p.subsemiring CharP.subsemiring

/- warning: char_p.subring -> CharP.subring is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] (p : Nat) [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))) p] (S : Subring.{u1} R _inst_1), CharP.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) (AddGroupWithOne.toAddMonoidWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) (Ring.toAddCommGroupWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) (Subring.toRing.{u1} R _inst_1 S)))) p
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R] (p : Nat) [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) p] (S : Subring.{u1} R _inst_1), CharP.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x S)) (AddGroupWithOne.toAddMonoidWithOne.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x S)) (Ring.toAddGroupWithOne.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x S)) (Subring.toRing.{u1} R _inst_1 S))) p
Case conversion may be inaccurate. Consider using '#align char_p.subring CharP.subringₓ'. -/
instance subring (R : Type u) [Ring R] (p : ℕ) [CharP R p] (S : Subring R) : CharP S p :=
  ⟨fun x =>
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h => Subtype.eq <| show S.Subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.Subtype x ▸ by rw [h, RingHom.map_zero]⟩⟩
#align char_p.subring CharP.subring

/- warning: char_p.subring' -> CharP.subring' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))) p] (S : Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)), CharP.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_1))) S) (AddGroupWithOne.toAddMonoidWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_1))) S) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_1))) S) (Ring.toAddCommGroupWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_1))) S) (Subring.toRing.{u1} R (CommRing.toRing.{u1} R _inst_1) S)))) p
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_2 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))) p] (S : Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)), CharP.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Subring.instSetLikeSubring.{u1} R (CommRing.toRing.{u1} R _inst_1))) x S)) (AddGroupWithOne.toAddMonoidWithOne.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Subring.instSetLikeSubring.{u1} R (CommRing.toRing.{u1} R _inst_1))) x S)) (Ring.toAddGroupWithOne.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Subring.instSetLikeSubring.{u1} R (CommRing.toRing.{u1} R _inst_1))) x S)) (Subring.toRing.{u1} R (CommRing.toRing.{u1} R _inst_1) S))) p
Case conversion may be inaccurate. Consider using '#align char_p.subring' CharP.subring'ₓ'. -/
instance subring' (R : Type u) [CommRing R] (p : ℕ) [CharP R p] (S : Subring R) : CharP S p :=
  CharP.subring R p S
#align char_p.subring' CharP.subring'

end CharP

