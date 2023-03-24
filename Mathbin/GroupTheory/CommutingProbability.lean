/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module group_theory.commuting_probability
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.ConjFinite
import Mathbin.GroupTheory.Abelianization
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.Index

/-!
# Commuting Probability

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file introduces the commuting probability of finite groups.

## Main definitions
* `comm_prob`: The commuting probability of a finite type with a multiplication operation.

## Todo
* Neumann's theorem.
-/


noncomputable section

open Classical

open BigOperators

open Fintype

variable (M : Type _) [Mul M]

#print commProb /-
/-- The commuting probability of a finite type with a multiplication operation -/
def commProb : ℚ :=
  Nat.card { p : M × M // p.1 * p.2 = p.2 * p.1 } / Nat.card M ^ 2
#align comm_prob commProb
-/

/- warning: comm_prob_def -> commProb_def is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Mul.{u1} M], Eq.{1} Rat (commProb.{u1} M _inst_1) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Nat.card.{u1} (Subtype.{succ u1} (Prod.{u1, u1} M M) (fun (p : Prod.{u1, u1} M M) => Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) (Prod.fst.{u1, u1} M M p) (Prod.snd.{u1, u1} M M p)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) (Prod.snd.{u1, u1} M M p) (Prod.fst.{u1, u1} M M p)))))) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Nat.card.{u1} M)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Mul.{u1} M], Eq.{1} Rat (commProb.{u1} M _inst_1) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Nat.card.{u1} (Subtype.{succ u1} (Prod.{u1, u1} M M) (fun (p : Prod.{u1, u1} M M) => Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) (Prod.fst.{u1, u1} M M p) (Prod.snd.{u1, u1} M M p)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) (Prod.snd.{u1, u1} M M p) (Prod.fst.{u1, u1} M M p)))))) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Nat.card.{u1} M)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align comm_prob_def commProb_defₓ'. -/
theorem commProb_def :
    commProb M = Nat.card { p : M × M // p.1 * p.2 = p.2 * p.1 } / Nat.card M ^ 2 :=
  rfl
#align comm_prob_def commProb_def

variable [Finite M]

#print commProb_pos /-
theorem commProb_pos [h : Nonempty M] : 0 < commProb M :=
  h.elim fun x =>
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)
#align comm_prob_pos commProb_pos
-/

/- warning: comm_prob_le_one -> commProb_le_one is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Mul.{u1} M] [_inst_2 : Finite.{succ u1} M], LE.le.{0} Rat Rat.hasLe (commProb.{u1} M _inst_1) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Mul.{u1} M] [_inst_2 : Finite.{succ u1} M], LE.le.{0} Rat Rat.instLERat (commProb.{u1} M _inst_1) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))
Case conversion may be inaccurate. Consider using '#align comm_prob_le_one commProb_le_oneₓ'. -/
theorem commProb_le_one : commProb M ≤ 1 :=
  by
  refine' div_le_one_of_le _ (sq_nonneg (Nat.card M))
  rw [← Nat.cast_pow, Nat.cast_le, sq, ← Nat.card_prod]
  apply Finite.card_subtype_le
#align comm_prob_le_one commProb_le_one

variable {M}

#print commProb_eq_one_iff /-
theorem commProb_eq_one_iff [h : Nonempty M] : commProb M = 1 ↔ Commutative ((· * ·) : M → M → M) :=
  by
  haveI := Fintype.ofFinite M
  rw [commProb, ← Set.coe_setOf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [div_eq_one_iff_eq, ← Nat.cast_pow, Nat.cast_inj, sq, ← card_prod,
    set_fintype_card_eq_univ_iff, Set.eq_univ_iff_forall]
  · exact ⟨fun h x y => h (x, y), fun h x => h x.1 x.2⟩
  · exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero)
#align comm_prob_eq_one_iff commProb_eq_one_iff
-/

variable (G : Type _) [Group G] [Finite G]

/- warning: card_comm_eq_card_conj_classes_mul_card -> card_comm_eq_card_conjClasses_mul_card is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [_inst_4 : Finite.{succ u1} G], Eq.{1} Nat (Nat.card.{u1} (Subtype.{succ u1} (Prod.{u1, u1} G G) (fun (p : Prod.{u1, u1} G G) => Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) (Prod.fst.{u1, u1} G G p) (Prod.snd.{u1, u1} G G p)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) (Prod.snd.{u1, u1} G G p) (Prod.fst.{u1, u1} G G p))))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Nat.card.{u1} (ConjClasses.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (Nat.card.{u1} G))
but is expected to have type
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [_inst_4 : Finite.{succ u1} G], Eq.{1} Nat (Nat.card.{u1} (Subtype.{succ u1} (Prod.{u1, u1} G G) (fun (p : Prod.{u1, u1} G G) => Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) (Prod.fst.{u1, u1} G G p) (Prod.snd.{u1, u1} G G p)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) (Prod.snd.{u1, u1} G G p) (Prod.fst.{u1, u1} G G p))))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Nat.card.{u1} (ConjClasses.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (Nat.card.{u1} G))
Case conversion may be inaccurate. Consider using '#align card_comm_eq_card_conj_classes_mul_card card_comm_eq_card_conjClasses_mul_cardₓ'. -/
theorem card_comm_eq_card_conjClasses_mul_card :
    Nat.card { p : G × G // p.1 * p.2 = p.2 * p.1 } = Nat.card (ConjClasses G) * Nat.card G :=
  by
  haveI := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card]
  convert calc
      card { p : G × G // p.1 * p.2 = p.2 * p.1 } = card (Σg, { h // g * h = h * g }) :=
        card_congr (Equiv.subtypeProdEquivSigmaSubtype fun g h : G => g * h = h * g)
      _ = ∑ g, card { h // g * h = h * g } := (card_sigma _)
      _ = ∑ g, card (MulAction.fixedBy (ConjAct G) G g) :=
        (sum_equiv conj_act.to_conj_act.to_equiv _ _ fun g =>
          card_congr' <| congr_arg _ <| funext fun h => mul_inv_eq_iff_eq_mul.symm.to_eq)
      _ = card (Quotient (MulAction.orbitRel (ConjAct G) G)) * card G :=
        (MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (ConjAct G) G)
      _ = card (Quotient (IsConj.setoid G)) * card G :=
        by
        have this : MulAction.orbitRel (ConjAct G) G = IsConj.setoid G :=
          Setoid.ext fun g h => (Setoid.comm' _).trans is_conj_iff.symm
        cc
      
#align card_comm_eq_card_conj_classes_mul_card card_comm_eq_card_conjClasses_mul_card

/- warning: comm_prob_def' -> commProb_def' is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [_inst_4 : Finite.{succ u1} G], Eq.{1} Rat (commProb.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Nat.card.{u1} (ConjClasses.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Nat.card.{u1} G)))
but is expected to have type
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [_inst_4 : Finite.{succ u1} G], Eq.{1} Rat (commProb.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Nat.card.{u1} (ConjClasses.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Nat.card.{u1} G)))
Case conversion may be inaccurate. Consider using '#align comm_prob_def' commProb_def'ₓ'. -/
theorem commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G :=
  by
  rw [commProb, card_comm_eq_card_conjClasses_mul_card, Nat.cast_mul, sq]
  exact mul_div_mul_right _ _ (nat.cast_ne_zero.mpr finite.card_pos.ne')
#align comm_prob_def' commProb_def'

variable {G} (H : Subgroup G)

/- warning: subgroup.comm_prob_subgroup_le -> Subgroup.commProb_subgroup_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] [_inst_4 : Finite.{succ u1} G] (H : Subgroup.{u1} G _inst_3), LE.le.{0} Rat Rat.hasLe (commProb.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) H) (Subgroup.mul.{u1} G _inst_3 H)) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) (commProb.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Subgroup.index.{u1} G _inst_3 H)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Finite.{succ u1} G] [_inst_4 : Group.{u1} G] (H : Subgroup.{u1} G _inst_4), LE.le.{0} Rat Rat.instLERat (commProb.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_4) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_4) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_4)) x H)) (Subgroup.mul.{u1} G _inst_4 H)) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (commProb.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) (HPow.hPow.{0, 0, 0} Rat Nat Rat (instHPow.{0, 0} Rat Nat (Monoid.Pow.{0} Rat Rat.monoid)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Subgroup.index.{u1} G _inst_4 H)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align subgroup.comm_prob_subgroup_le Subgroup.commProb_subgroup_leₓ'. -/
theorem Subgroup.commProb_subgroup_le : commProb H ≤ commProb G * H.index ^ 2 :=
  by
  /- After rewriting with `comm_prob_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def, commProb_def, div_le_iff, mul_assoc, ← mul_pow, ← Nat.cast_mul,
    mul_comm H.index, H.card_mul_index, div_mul_cancel, Nat.cast_le]
  · refine' Finite.card_le_of_injective (fun p => ⟨⟨p.1.1, p.1.2⟩, subtype.ext_iff.mp p.2⟩) _
    exact fun p q h => by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_ne_zero 2 (nat.cast_ne_zero.mpr finite.card_pos.ne')
  · exact pow_pos (nat.cast_pos.mpr Finite.card_pos) 2
#align subgroup.comm_prob_subgroup_le Subgroup.commProb_subgroup_le

/- warning: subgroup.comm_prob_quotient_le -> Subgroup.commProb_quotient_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] [_inst_4 : Finite.{succ u1} G] (H : Subgroup.{u1} G _inst_3) [_inst_5 : Subgroup.Normal.{u1} G _inst_3 H], LE.le.{0} Rat Rat.hasLe (commProb.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_3) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_3) H) (MulOneClass.toHasMul.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_3) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_3) H) (Monoid.toMulOneClass.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_3) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_3) H) (DivInvMonoid.toMonoid.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_3) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_3) H) (Group.toDivInvMonoid.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_3) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_3) H) (QuotientGroup.Quotient.group.{u1} G _inst_3 H _inst_5)))))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) (commProb.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) H))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Finite.{succ u1} G] [_inst_4 : Group.{u1} G] (H : Subgroup.{u1} G _inst_4) [_inst_5 : Subgroup.Normal.{u1} G _inst_4 H], LE.le.{0} Rat Rat.instLERat (commProb.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_4) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_4) H) (MulOneClass.toMul.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_4) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_4) H) (Monoid.toMulOneClass.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_4) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_4) H) (DivInvMonoid.toMonoid.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_4) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_4) H) (Group.toDivInvMonoid.{u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_4) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_4) H) (QuotientGroup.Quotient.group.{u1} G _inst_4 H _inst_5)))))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (commProb.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4))))) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Nat.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_4) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_4) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_4)) x H)))))
Case conversion may be inaccurate. Consider using '#align subgroup.comm_prob_quotient_le Subgroup.commProb_quotient_leₓ'. -/
theorem Subgroup.commProb_quotient_le [H.Normal] : commProb (G ⧸ H) ≤ commProb G * Nat.card H :=
  by
  /- After rewriting with `comm_prob_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def', commProb_def', div_le_iff, mul_assoc, ← Nat.cast_mul, ← Subgroup.index,
    H.card_mul_index, div_mul_cancel, Nat.cast_le]
  · apply Finite.card_le_of_surjective
    show Function.Surjective (ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.surjective_Quotient_mk''
  · exact nat.cast_ne_zero.mpr finite.card_pos.ne'
  · exact nat.cast_pos.mpr Finite.card_pos
#align subgroup.comm_prob_quotient_le Subgroup.commProb_quotient_le

variable (G)

/- warning: inv_card_commutator_le_comm_prob -> inv_card_commutator_le_commProb is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_3 : Group.{u1} G] [_inst_4 : Finite.{succ u1} G], LE.le.{0} Rat Rat.hasLe (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) (commutator.{u1} G _inst_3))))) (commProb.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_3 : Finite.{succ u1} G] [_inst_4 : Group.{u1} G], LE.le.{0} Rat Rat.instLERat (Inv.inv.{0} Rat Rat.instInvRat (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Nat.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_4) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_4) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_4)) x (commutator.{u1} G _inst_4)))))) (commProb.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_4)))))
Case conversion may be inaccurate. Consider using '#align inv_card_commutator_le_comm_prob inv_card_commutator_le_commProbₓ'. -/
theorem inv_card_commutator_le_commProb : (↑(Nat.card (commutator G)))⁻¹ ≤ commProb G :=
  (inv_pos_le_iff_one_le_mul (nat.cast_pos.mpr Finite.card_pos)).mpr
    (le_trans (ge_of_eq (commProb_eq_one_iff.mpr (Abelianization.commGroup G).mul_comm))
      (commutator G).commProb_quotient_le)
#align inv_card_commutator_le_comm_prob inv_card_commutator_le_commProb

