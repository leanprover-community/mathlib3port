/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning

! This file was ported from Lean 3 source module group_theory.p_group
! leanprover-community/mathlib commit f694c7dead66f5d4c80f446c796a5aad14707f0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.Index
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.Perm.Cycle.Type
import Mathbin.GroupTheory.SpecificGroups.Cyclic
import Mathbin.Tactic.IntervalCases

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/


open BigOperators

open Fintype MulAction

variable (p : ℕ) (G : Type _) [Group G]

#print IsPGroup /-
/-- A p-group is a group in which every element has prime power order -/
def IsPGroup : Prop :=
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1
#align is_p_group IsPGroup
-/

variable {p} {G}

namespace IsPGroup

#print IsPGroup.iff_orderOf /-
theorem iff_orderOf [hp : Fact p.Prime] : IsPGroup p G ↔ ∀ g : G, ∃ k : ℕ, orderOf g = p ^ k :=
  forall_congr' fun g =>
    ⟨fun ⟨k, hk⟩ =>
      Exists.imp (fun j => Exists.snd)
        ((Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hk)),
      Exists.imp fun k hk => by rw [← hk, pow_orderOf_eq_one]⟩
#align is_p_group.iff_order_of IsPGroup.iff_orderOf
-/

#print IsPGroup.of_card /-
theorem of_card [Fintype G] {n : ℕ} (hG : card G = p ^ n) : IsPGroup p G := fun g =>
  ⟨n, by rw [← hG, pow_card_eq_one]⟩
#align is_p_group.of_card IsPGroup.of_card
-/

/- warning: is_p_group.of_bot -> IsPGroup.of_bot is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1))) (Subgroup.toGroup.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)))) (Subgroup.toGroup.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_p_group.of_bot IsPGroup.of_botₓ'. -/
theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  of_card (Subgroup.card_bot.trans (pow_zero p).symm)
#align is_p_group.of_bot IsPGroup.of_bot

#print IsPGroup.iff_card /-
theorem iff_card [Fact p.Prime] [Fintype G] : IsPGroup p G ↔ ∃ n : ℕ, card G = p ^ n :=
  by
  have hG : card G ≠ 0 := card_ne_zero
  refine' ⟨fun h => _, fun ⟨n, hn⟩ => of_card hn⟩
  suffices ∀ q ∈ Nat.factors (card G), q = p
    by
    use (card G).factors.length
    rw [← List.prod_replicate, ← List.eq_replicate_of_mem this, Nat.prod_factors hG]
  intro q hq
  obtain ⟨hq1, hq2⟩ := (Nat.mem_factors hG).mp hq
  haveI : Fact q.prime := ⟨hq1⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card q hq2
  obtain ⟨k, hk⟩ := (iff_order_of.mp h) g
  exact (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm
#align is_p_group.iff_card IsPGroup.iff_card
-/

section GIsPGroup

variable (hG : IsPGroup p G)

include hG

/- warning: is_p_group.of_injective -> IsPGroup.of_injective is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall {H : Type.{u2}} [_inst_2 : Group.{u2} H] (ϕ : MonoidHom.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))), (Function.Injective.{succ u2, succ u1} H G (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (fun (_x : MonoidHom.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) => H -> G) (MonoidHom.hasCoeToFun.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) ϕ)) -> (IsPGroup.{u2} p H _inst_2))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall {H : Type.{u2}} [_inst_2 : Group.{u2} H] (ϕ : MonoidHom.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))), (Function.Injective.{succ u2, succ u1} H G (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) H (fun (_x : H) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : H) => G) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) H G (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MonoidHom.monoidHomClass.{u2, u1} H G (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) ϕ)) -> (IsPGroup.{u2} p H _inst_2))
Case conversion may be inaccurate. Consider using '#align is_p_group.of_injective IsPGroup.of_injectiveₓ'. -/
theorem of_injective {H : Type _} [Group H] (ϕ : H →* G) (hϕ : Function.Injective ϕ) :
    IsPGroup p H := by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)
#align is_p_group.of_injective IsPGroup.of_injective

/- warning: is_p_group.to_subgroup -> IsPGroup.to_subgroup is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall (H : Subgroup.{u1} G _inst_1), IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall (H : Subgroup.{u1} G _inst_1), IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align is_p_group.to_subgroup IsPGroup.to_subgroupₓ'. -/
theorem to_subgroup (H : Subgroup G) : IsPGroup p H :=
  hG.of_injective H.Subtype Subtype.coe_injective
#align is_p_group.to_subgroup IsPGroup.to_subgroup

/- warning: is_p_group.of_surjective -> IsPGroup.of_surjective is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall {H : Type.{u2}} [_inst_2 : Group.{u2} H] (ϕ : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))), (Function.Surjective.{succ u1, succ u2} G H (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) ϕ)) -> (IsPGroup.{u2} p H _inst_2))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall {H : Type.{u2}} [_inst_2 : Group.{u2} H] (ϕ : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))), (Function.Surjective.{succ u1, succ u2} G H (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => H) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))))) ϕ)) -> (IsPGroup.{u2} p H _inst_2))
Case conversion may be inaccurate. Consider using '#align is_p_group.of_surjective IsPGroup.of_surjectiveₓ'. -/
theorem of_surjective {H : Type _} [Group H] (ϕ : G →* H) (hϕ : Function.Surjective ϕ) :
    IsPGroup p H :=
  by
  refine' fun h => Exists.elim (hϕ h) fun g hg => Exists.imp (fun k hk => _) (hG g)
  rw [← hg, ← ϕ.map_pow, hk, ϕ.map_one]
#align is_p_group.of_surjective IsPGroup.of_surjective

#print IsPGroup.to_quotient /-
theorem to_quotient (H : Subgroup G) [H.Normal] : IsPGroup p (G ⧸ H) :=
  hG.ofSurjective (QuotientGroup.mk' H) Quotient.surjective_Quotient_mk''
#align is_p_group.to_quotient IsPGroup.to_quotient
-/

/- warning: is_p_group.of_equiv -> IsPGroup.of_equiv is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall {H : Type.{u2}} [_inst_2 : Group.{u2} H], (MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))))) -> (IsPGroup.{u2} p H _inst_2))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall {H : Type.{u2}} [_inst_2 : Group.{u2} H], (MulEquiv.{u1, u2} G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))))) -> (IsPGroup.{u2} p H _inst_2))
Case conversion may be inaccurate. Consider using '#align is_p_group.of_equiv IsPGroup.of_equivₓ'. -/
theorem of_equiv {H : Type _} [Group H] (ϕ : G ≃* H) : IsPGroup p H :=
  hG.ofSurjective ϕ.toMonoidHom ϕ.Surjective
#align is_p_group.of_equiv IsPGroup.of_equiv

#print IsPGroup.orderOf_coprime /-
theorem orderOf_coprime {n : ℕ} (hn : p.coprime n) (g : G) : (orderOf g).coprime n :=
  let ⟨k, hk⟩ := hG g
  (hn.pow_leftₓ k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)
#align is_p_group.order_of_coprime IsPGroup.orderOf_coprime
-/

#print IsPGroup.powEquiv /-
/-- If `gcd(p,n) = 1`, then the `n`th power map is a bijection. -/
noncomputable def powEquiv {n : ℕ} (hn : p.coprime n) : G ≃ G :=
  let h : ∀ g : G, (Nat.card (Subgroup.zpowers g)).coprime n := fun g =>
    order_eq_card_zpowers' g ▸ hG.orderOf_coprime hn g
  { toFun := (· ^ n)
    invFun := fun g => (powCoprime (h g)).symm ⟨g, Subgroup.mem_zpowers g⟩
    left_inv := fun g =>
      Subtype.ext_iff.1 <|
        (powCoprime (h (g ^ n))).left_inv
          ⟨g, _, Subtype.ext_iff.1 <| (powCoprime (h g)).left_inv ⟨g, Subgroup.mem_zpowers g⟩⟩
    right_inv := fun g =>
      Subtype.ext_iff.1 <| (powCoprime (h g)).right_inv ⟨g, Subgroup.mem_zpowers g⟩ }
#align is_p_group.pow_equiv IsPGroup.powEquiv
-/

#print IsPGroup.powEquiv_apply /-
@[simp]
theorem powEquiv_apply {n : ℕ} (hn : p.coprime n) (g : G) : hG.powEquiv hn g = g ^ n :=
  rfl
#align is_p_group.pow_equiv_apply IsPGroup.powEquiv_apply
-/

#print IsPGroup.powEquiv_symm_apply /-
@[simp]
theorem powEquiv_symm_apply {n : ℕ} (hn : p.coprime n) (g : G) :
    (hG.powEquiv hn).symm g = g ^ (orderOf g).gcdB n := by rw [order_eq_card_zpowers'] <;> rfl
#align is_p_group.pow_equiv_symm_apply IsPGroup.powEquiv_symm_apply
-/

variable [hp : Fact p.Prime]

include hp

#print IsPGroup.powEquiv' /-
/-- If `p ∤ n`, then the `n`th power map is a bijection. -/
@[reducible]
noncomputable def powEquiv' {n : ℕ} (hn : ¬p ∣ n) : G ≃ G :=
  powEquiv hG (hp.out.coprime_iff_not_dvd.mpr hn)
#align is_p_group.pow_equiv' IsPGroup.powEquiv'
-/

#print IsPGroup.index /-
theorem index (H : Subgroup G) [H.FiniteIndex] : ∃ n : ℕ, H.index = p ^ n :=
  by
  haveI := H.normal_core.fintype_quotient_of_finite_index
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normal_core)
  obtain ⟨k, hk1, hk2⟩ :=
    (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ (H.normal_core.index_eq_card.trans hn)).mp
        (Subgroup.index_dvd_of_le H.normal_core_le))
  exact ⟨k, hk2⟩
#align is_p_group.index IsPGroup.index
-/

#print IsPGroup.card_eq_or_dvd /-
theorem card_eq_or_dvd : Nat.card G = 1 ∨ p ∣ Nat.card G :=
  by
  cases fintypeOrInfinite G
  · obtain ⟨n, hn⟩ := iff_card.mp hG
    rw [Nat.card_eq_fintype_card, hn]
    cases n
    · exact Or.inl rfl
    · exact Or.inr ⟨p ^ n, rfl⟩
  · rw [Nat.card_eq_zero_of_infinite]
    exact Or.inr ⟨0, rfl⟩
#align is_p_group.card_eq_or_dvd IsPGroup.card_eq_or_dvd
-/

/- warning: is_p_group.nontrivial_iff_card -> IsPGroup.nontrivial_iff_card is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall [hp : Fact (Nat.Prime p)] [_inst_2 : Fintype.{u1} G], Iff (Nontrivial.{u1} G) (Exists.{1} Nat (fun (n : Nat) => Exists.{0} (GT.gt.{0} Nat Nat.hasLt n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (H : GT.gt.{0} Nat Nat.hasLt n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Eq.{1} Nat (Fintype.card.{u1} G _inst_2) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n)))))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall [hp : Fact (Nat.Prime p)] [_inst_2 : Fintype.{u1} G], Iff (Nontrivial.{u1} G) (Exists.{1} Nat (fun (n : Nat) => And (GT.gt.{0} Nat instLTNat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Eq.{1} Nat (Fintype.card.{u1} G _inst_2) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)))))
Case conversion may be inaccurate. Consider using '#align is_p_group.nontrivial_iff_card IsPGroup.nontrivial_iff_cardₓ'. -/
theorem nontrivial_iff_card [Fintype G] : Nontrivial G ↔ ∃ n > 0, card G = p ^ n :=
  ⟨fun hGnt =>
    let ⟨k, hk⟩ := iff_card.1 hG
    ⟨k,
      Nat.pos_of_ne_zero fun hk0 => by
        rw [hk0, pow_zero] at hk <;> exact fintype.one_lt_card.ne' hk,
      hk⟩,
    fun ⟨k, hk0, hk⟩ =>
    one_lt_card_iff_nontrivial.1 <| hk.symm ▸ one_lt_pow (Fact.out p.Prime).one_lt (ne_of_gt hk0)⟩
#align is_p_group.nontrivial_iff_card IsPGroup.nontrivial_iff_card

variable {α : Type _} [MulAction G α]

#print IsPGroup.card_orbit /-
theorem card_orbit (a : α) [Fintype (orbit G a)] : ∃ n : ℕ, card (orbit G a) = p ^ n :=
  by
  let ϕ := orbit_equiv_quotient_stabilizer G a
  haveI := Fintype.ofEquiv (orbit G a) ϕ
  haveI := (stabilizer G a).finiteIndex_of_finite_quotient
  rw [card_congr ϕ, ← Subgroup.index_eq_card]
  exact hG.index (stabilizer G a)
#align is_p_group.card_orbit IsPGroup.card_orbit
-/

variable (α) [Fintype α]

#print IsPGroup.card_modEq_card_fixedPoints /-
/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
theorem card_modEq_card_fixedPoints [Fintype (fixedPoints G α)] :
    card α ≡ card (fixedPoints G α) [MOD p] := by
  classical
    calc
      card α = card (Σy : Quotient (orbit_rel G α), { x // Quotient.mk'' x = y }) :=
        card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbit_rel G α))).symm
      _ = ∑ a : Quotient (orbit_rel G α), card { x // Quotient.mk'' x = a } := (card_sigma _)
      _ ≡ ∑ a : fixed_points G α, 1 [MOD p] := _
      _ = _ := by simp <;> rfl
      
    rw [← ZMod.eq_iff_modEq_nat p, Nat.cast_sum, Nat.cast_sum]
    have key :
      ∀ x,
        card { y // (Quotient.mk'' y : Quotient (orbit_rel G α)) = Quotient.mk'' x } =
          card (orbit G x) :=
      fun x => by simp only [Quotient.eq''] <;> congr
    refine'
      Eq.symm
        (Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.1) (fun _ _ _ => Finset.mem_univ _)
          (fun a₁ a₂ _ _ _ _ h =>
            Subtype.eq ((mem_fixed_points' α).mp a₂.2 a₁.1 (Quotient.exact' h)))
          (fun b => Quotient.inductionOn' b fun b _ hb => _) fun a ha _ => by
          rw [key, mem_fixed_points_iff_card_orbit_eq_one.mp a.2])
    obtain ⟨k, hk⟩ := hG.card_orbit b
    have : k = 0 :=
      le_zero_iff.1
        (Nat.le_of_lt_succ
          (lt_of_not_ge
            (mt (pow_dvd_pow p)
              (by
                rwa [pow_one, ← hk, ← Nat.modEq_zero_iff_dvd, ← ZMod.eq_iff_modEq_nat, ← key,
                  Nat.cast_zero]))))
    exact
      ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 <| by rw [hk, this, pow_zero]⟩,
        Finset.mem_univ _, ne_of_eq_of_ne Nat.cast_one one_ne_zero, rfl⟩
#align is_p_group.card_modeq_card_fixed_points IsPGroup.card_modEq_card_fixedPoints
-/

#print IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card /-
/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
theorem nonempty_fixed_point_of_prime_not_dvd_card (hpα : ¬p ∣ card α) [Finite (fixedPoints G α)] :
    (fixedPoints G α).Nonempty :=
  @Set.nonempty_of_nonempty_subtype _ _
    (by
      cases nonempty_fintype (fixed_points G α)
      rw [← card_pos_iff, pos_iff_ne_zero]
      contrapose! hpα
      rw [← Nat.modEq_zero_iff_dvd, ← hpα]
      exact hG.card_modeq_card_fixed_points α)
#align is_p_group.nonempty_fixed_point_of_prime_not_dvd_card IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card
-/

#print IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point /-
/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
theorem exists_fixed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ card α) {a : α}
    (ha : a ∈ fixedPoints G α) : ∃ b, b ∈ fixedPoints G α ∧ a ≠ b :=
  by
  cases nonempty_fintype (fixed_points G α)
  have hpf : p ∣ card (fixed_points G α) :=
    nat.modeq_zero_iff_dvd.mp ((hG.card_modeq_card_fixed_points α).symm.trans hpα.modeq_zero_nat)
  have hα : 1 < card (fixed_points G α) :=
    (Fact.out p.prime).one_lt.trans_le (Nat.le_of_dvd (card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  exact
    let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩
    ⟨b, hb, fun hab => hba (by simp_rw [hab])⟩
#align is_p_group.exists_fixed_point_of_prime_dvd_card_of_fixed_point IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
-/

/- warning: is_p_group.center_nontrivial -> IsPGroup.center_nontrivial is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall [hp : Fact (Nat.Prime p)] [_inst_4 : Nontrivial.{u1} G] [_inst_5 : Finite.{succ u1} G], Nontrivial.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall [hp : Fact (Nat.Prime p)] [_inst_4 : Nontrivial.{u1} G] [_inst_5 : Finite.{succ u1} G], Nontrivial.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Subgroup.center.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align is_p_group.center_nontrivial IsPGroup.center_nontrivialₓ'. -/
theorem center_nontrivial [Nontrivial G] [Finite G] : Nontrivial (Subgroup.center G) := by
  classical
    cases nonempty_fintype G
    have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
    rw [ConjAct.fixedPoints_eq_center] at this
    obtain ⟨g, hg⟩ := this _ (Subgroup.center G).one_mem
    · exact ⟨⟨1, ⟨g, hg.1⟩, mt subtype.ext_iff.mp hg.2⟩⟩
    · obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
      exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
#align is_p_group.center_nontrivial IsPGroup.center_nontrivial

/- warning: is_p_group.bot_lt_center -> IsPGroup.bot_lt_center is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall [hp : Fact (Nat.Prime p)] [_inst_4 : Nontrivial.{u1} G] [_inst_5 : Finite.{succ u1} G], LT.lt.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toHasLt.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G], (IsPGroup.{u1} p G _inst_1) -> (forall [hp : Fact (Nat.Prime p)] [_inst_4 : Nontrivial.{u1} G] [_inst_5 : Finite.{succ u1} G], LT.lt.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLT.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align is_p_group.bot_lt_center IsPGroup.bot_lt_centerₓ'. -/
theorem bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Subgroup.center G :=
  by
  haveI := center_nontrivial hG
  cases nonempty_fintype G
  classical exact
      bot_lt_iff_ne_bot.mpr ((Subgroup.center G).one_lt_card_iff_ne_bot.mp Fintype.one_lt_card)
#align is_p_group.bot_lt_center IsPGroup.bot_lt_center

end GIsPGroup

/- warning: is_p_group.to_le -> IsPGroup.to_le is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toHasLe.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align is_p_group.to_le IsPGroup.to_leₓ'. -/
theorem to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H ≤ K) : IsPGroup p H :=
  hK.of_injective (Subgroup.inclusion hHK) fun a b h =>
    Subtype.ext (show _ from Subtype.ext_iff.mp h)
#align is_p_group.to_le IsPGroup.to_le

/- warning: is_p_group.to_inf_left -> IsPGroup.to_inf_left is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K)) (Subgroup.toGroup.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K))) (Subgroup.toGroup.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K)))
Case conversion may be inaccurate. Consider using '#align is_p_group.to_inf_left IsPGroup.to_inf_leftₓ'. -/
theorem to_inf_left {H K : Subgroup G} (hH : IsPGroup p H) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hH.to_le inf_le_left
#align is_p_group.to_inf_left IsPGroup.to_inf_left

/- warning: is_p_group.to_inf_right -> IsPGroup.to_inf_right is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K)) (Subgroup.toGroup.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K))) (Subgroup.toGroup.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K)))
Case conversion may be inaccurate. Consider using '#align is_p_group.to_inf_right IsPGroup.to_inf_rightₓ'. -/
theorem to_inf_right {H K : Subgroup G} (hK : IsPGroup p K) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hK.to_le inf_le_right
#align is_p_group.to_inf_right IsPGroup.to_inf_right

/- warning: is_p_group.map -> IsPGroup.map is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (forall {K : Type.{u2}} [_inst_2 : Group.{u2} K] (ϕ : MonoidHom.{u1, u2} G K (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2)))), IsPGroup.{u2} p (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} K _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} K _inst_2) K (Subgroup.setLike.{u2} K _inst_2)) (Subgroup.map.{u1, u2} G _inst_1 K _inst_2 ϕ H)) (Subgroup.toGroup.{u2} K _inst_2 (Subgroup.map.{u1, u2} G _inst_1 K _inst_2 ϕ H)))
but is expected to have type
  forall {p : Nat} {G : Type.{u2}} [_inst_1 : Group.{u2} G] {H : Subgroup.{u2} G _inst_1}, (IsPGroup.{u2} p (Subtype.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) x H)) (Subgroup.toGroup.{u2} G _inst_1 H)) -> (forall {K : Type.{u1}} [_inst_2 : Group.{u1} K] (ϕ : MonoidHom.{u2, u1} G K (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2)))), IsPGroup.{u1} p (Subtype.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Subgroup.{u1} K _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} K _inst_2) K (Subgroup.instSetLikeSubgroup.{u1} K _inst_2)) x (Subgroup.map.{u2, u1} G _inst_1 K _inst_2 ϕ H))) (Subgroup.toGroup.{u1} K _inst_2 (Subgroup.map.{u2, u1} G _inst_1 K _inst_2 ϕ H)))
Case conversion may be inaccurate. Consider using '#align is_p_group.map IsPGroup.mapₓ'. -/
theorem map {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Group K] (ϕ : G →* K) :
    IsPGroup p (H.map ϕ) := by
  rw [← H.subtype_range, MonoidHom.map_range]
  exact hH.of_surjective (ϕ.restrict H).range_restrict (ϕ.restrict H).rangeRestrict_surjective
#align is_p_group.map IsPGroup.map

/- warning: is_p_group.comap_of_ker_is_p_group -> IsPGroup.comap_of_ker_isPGroup is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (forall {K : Type.{u2}} [_inst_2 : Group.{u2} K] (ϕ : MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))), (IsPGroup.{u2} p (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} K _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} K _inst_2) K (Subgroup.setLike.{u2} K _inst_2)) (MonoidHom.ker.{u2, u1} K _inst_2 G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) ϕ)) (Subgroup.toGroup.{u2} K _inst_2 (MonoidHom.ker.{u2, u1} K _inst_2 G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) ϕ))) -> (IsPGroup.{u2} p (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} K _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} K _inst_2) K (Subgroup.setLike.{u2} K _inst_2)) (Subgroup.comap.{u2, u1} K _inst_2 G _inst_1 ϕ H)) (Subgroup.toGroup.{u2} K _inst_2 (Subgroup.comap.{u2, u1} K _inst_2 G _inst_1 ϕ H))))
but is expected to have type
  forall {p : Nat} {G : Type.{u2}} [_inst_1 : Group.{u2} G] {H : Subgroup.{u2} G _inst_1}, (IsPGroup.{u2} p (Subtype.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) x H)) (Subgroup.toGroup.{u2} G _inst_1 H)) -> (forall {K : Type.{u1}} [_inst_2 : Group.{u1} K] (ϕ : MonoidHom.{u1, u2} K G (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))), (IsPGroup.{u1} p (Subtype.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Subgroup.{u1} K _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} K _inst_2) K (Subgroup.instSetLikeSubgroup.{u1} K _inst_2)) x (MonoidHom.ker.{u1, u2} K _inst_2 G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) ϕ))) (Subgroup.toGroup.{u1} K _inst_2 (MonoidHom.ker.{u1, u2} K _inst_2 G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) ϕ))) -> (IsPGroup.{u1} p (Subtype.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Subgroup.{u1} K _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} K _inst_2) K (Subgroup.instSetLikeSubgroup.{u1} K _inst_2)) x (Subgroup.comap.{u1, u2} K _inst_2 G _inst_1 ϕ H))) (Subgroup.toGroup.{u1} K _inst_2 (Subgroup.comap.{u1, u2} K _inst_2 G _inst_1 ϕ H))))
Case conversion may be inaccurate. Consider using '#align is_p_group.comap_of_ker_is_p_group IsPGroup.comap_of_ker_isPGroupₓ'. -/
theorem comap_of_ker_isPGroup {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Group K]
    (ϕ : K →* G) (hϕ : IsPGroup p ϕ.ker) : IsPGroup p (H.comap ϕ) :=
  by
  intro g
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
  rw [Subtype.ext_iff, H.coe_pow, Subtype.coe_mk, ← ϕ.map_pow] at hj
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩
  rwa [Subtype.ext_iff, ϕ.ker.coe_pow, Subtype.coe_mk, ← pow_mul, ← pow_add] at hk
  exact ⟨j + k, by rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩
#align is_p_group.comap_of_ker_is_p_group IsPGroup.comap_of_ker_isPGroup

/- warning: is_p_group.ker_is_p_group_of_injective -> IsPGroup.ker_isPGroup_of_injective is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {K : Type.{u2}} [_inst_2 : Group.{u2} K] {ϕ : MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))}, (Function.Injective.{succ u2, succ u1} K G (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (fun (_x : MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) => K -> G) (MonoidHom.hasCoeToFun.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) ϕ)) -> (IsPGroup.{u2} p (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} K _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} K _inst_2) K (Subgroup.setLike.{u2} K _inst_2)) (MonoidHom.ker.{u2, u1} K _inst_2 G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) ϕ)) (Subgroup.toGroup.{u2} K _inst_2 (MonoidHom.ker.{u2, u1} K _inst_2 G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) ϕ)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {K : Type.{u2}} [_inst_2 : Group.{u2} K] {ϕ : MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))}, (Function.Injective.{succ u2, succ u1} K G (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) K (fun (_x : K) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : K) => G) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) K G (MulOneClass.toMul.{u2} K (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2)))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MonoidHom.monoidHomClass.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) ϕ)) -> (IsPGroup.{u2} p (Subtype.{succ u2} K (fun (x : K) => Membership.mem.{u2, u2} K (Subgroup.{u2} K _inst_2) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} K _inst_2) K (Subgroup.instSetLikeSubgroup.{u2} K _inst_2)) x (MonoidHom.ker.{u2, u1} K _inst_2 G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) ϕ))) (Subgroup.toGroup.{u2} K _inst_2 (MonoidHom.ker.{u2, u1} K _inst_2 G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) ϕ)))
Case conversion may be inaccurate. Consider using '#align is_p_group.ker_is_p_group_of_injective IsPGroup.ker_isPGroup_of_injectiveₓ'. -/
theorem ker_isPGroup_of_injective {K : Type _} [Group K] {ϕ : K →* G} (hϕ : Function.Injective ϕ) :
    IsPGroup p ϕ.ker :=
  (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot_iff.mpr hϕ)).mpr IsPGroup.of_bot
#align is_p_group.ker_is_p_group_of_injective IsPGroup.ker_isPGroup_of_injective

/- warning: is_p_group.comap_of_injective -> IsPGroup.comap_of_injective is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (forall {K : Type.{u2}} [_inst_2 : Group.{u2} K] (ϕ : MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))), (Function.Injective.{succ u2, succ u1} K G (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (fun (_x : MonoidHom.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) => K -> G) (MonoidHom.hasCoeToFun.{u2, u1} K G (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) ϕ)) -> (IsPGroup.{u2} p (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} K _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} K _inst_2) K (Subgroup.setLike.{u2} K _inst_2)) (Subgroup.comap.{u2, u1} K _inst_2 G _inst_1 ϕ H)) (Subgroup.toGroup.{u2} K _inst_2 (Subgroup.comap.{u2, u1} K _inst_2 G _inst_1 ϕ H))))
but is expected to have type
  forall {p : Nat} {G : Type.{u2}} [_inst_1 : Group.{u2} G] {H : Subgroup.{u2} G _inst_1}, (IsPGroup.{u2} p (Subtype.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) x H)) (Subgroup.toGroup.{u2} G _inst_1 H)) -> (forall {K : Type.{u1}} [_inst_2 : Group.{u1} K] (ϕ : MonoidHom.{u1, u2} K G (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))), (Function.Injective.{succ u1, succ u2} K G (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MonoidHom.{u1, u2} K G (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) K (fun (_x : K) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : K) => G) _x) (MulHomClass.toFunLike.{max u2 u1, u1, u2} (MonoidHom.{u1, u2} K G (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) K G (MulOneClass.toMul.{u1} K (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2)))) (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u1, u2} (MonoidHom.{u1, u2} K G (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) K G (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (MonoidHom.monoidHomClass.{u1, u2} K G (Monoid.toMulOneClass.{u1} K (DivInvMonoid.toMonoid.{u1} K (Group.toDivInvMonoid.{u1} K _inst_2))) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))))) ϕ)) -> (IsPGroup.{u1} p (Subtype.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Subgroup.{u1} K _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} K _inst_2) K (Subgroup.instSetLikeSubgroup.{u1} K _inst_2)) x (Subgroup.comap.{u1, u2} K _inst_2 G _inst_1 ϕ H))) (Subgroup.toGroup.{u1} K _inst_2 (Subgroup.comap.{u1, u2} K _inst_2 G _inst_1 ϕ H))))
Case conversion may be inaccurate. Consider using '#align is_p_group.comap_of_injective IsPGroup.comap_of_injectiveₓ'. -/
theorem comap_of_injective {H : Subgroup G} (hH : IsPGroup p H) {K : Type _} [Group K] (ϕ : K →* G)
    (hϕ : Function.Injective ϕ) : IsPGroup p (H.comap ϕ) :=
  hH.comap_of_ker_isPGroup ϕ (ker_isPGroup_of_injective hϕ)
#align is_p_group.comap_of_injective IsPGroup.comap_of_injective

/- warning: is_p_group.comap_subtype -> IsPGroup.comap_subtype is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (forall {K : Subgroup.{u1} G _inst_1}, IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.setLike.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K))) (Subgroup.comap.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K) G _inst_1 (Subgroup.subtype.{u1} G _inst_1 K) H)) (Subgroup.toGroup.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K) (Subgroup.comap.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K) G _inst_1 (Subgroup.subtype.{u1} G _inst_1 K) H)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (forall {K : Subgroup.{u1} G _inst_1}, IsPGroup.{u1} p (Subtype.{succ u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (fun (x : Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) => Membership.mem.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.instSetLikeSubgroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K))) x (Subgroup.comap.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K) G _inst_1 (Subgroup.subtype.{u1} G _inst_1 K) H))) (Subgroup.toGroup.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K) (Subgroup.comap.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K) G _inst_1 (Subgroup.subtype.{u1} G _inst_1 K) H)))
Case conversion may be inaccurate. Consider using '#align is_p_group.comap_subtype IsPGroup.comap_subtypeₓ'. -/
theorem comap_subtype {H : Subgroup G} (hH : IsPGroup p H) {K : Subgroup G} :
    IsPGroup p (H.comap K.Subtype) :=
  hH.comap_of_injective K.Subtype Subtype.coe_injective
#align is_p_group.comap_subtype IsPGroup.comap_subtype

/- warning: is_p_group.to_sup_of_normal_right -> IsPGroup.to_sup_of_normal_right is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (forall [_inst_2 : Subgroup.Normal.{u1} G _inst_1 K], IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)) (Subgroup.toGroup.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (forall [_inst_2 : Subgroup.Normal.{u1} G _inst_1 K], IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K))) (Subgroup.toGroup.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K)))
Case conversion may be inaccurate. Consider using '#align is_p_group.to_sup_of_normal_right IsPGroup.to_sup_of_normal_rightₓ'. -/
theorem to_sup_of_normal_right {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [K.Normal] : IsPGroup p (H ⊔ K : Subgroup G) :=
  by
  rw [← QuotientGroup.ker_mk' K, ← Subgroup.comap_map_eq]
  apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_isPGroup
  rwa [QuotientGroup.ker_mk']
#align is_p_group.to_sup_of_normal_right IsPGroup.to_sup_of_normal_right

/- warning: is_p_group.to_sup_of_normal_left -> IsPGroup.to_sup_of_normal_left is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (forall [_inst_2 : Subgroup.Normal.{u1} G _inst_1 H], IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)) (Subgroup.toGroup.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (forall [_inst_2 : Subgroup.Normal.{u1} G _inst_1 H], IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K))) (Subgroup.toGroup.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K)))
Case conversion may be inaccurate. Consider using '#align is_p_group.to_sup_of_normal_left IsPGroup.to_sup_of_normal_leftₓ'. -/
theorem to_sup_of_normal_left {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [H.Normal] : IsPGroup p (H ⊔ K : Subgroup G) :=
  (congr_arg (fun H : Subgroup G => IsPGroup p H) sup_comm).mp (to_sup_of_normal_right hK hH)
#align is_p_group.to_sup_of_normal_left IsPGroup.to_sup_of_normal_left

/- warning: is_p_group.to_sup_of_normal_right' -> IsPGroup.to_sup_of_normal_right' is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toHasLe.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H (Subgroup.normalizer.{u1} G _inst_1 K)) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)) (Subgroup.toGroup.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H (Subgroup.normalizer.{u1} G _inst_1 K)) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K))) (Subgroup.toGroup.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K)))
Case conversion may be inaccurate. Consider using '#align is_p_group.to_sup_of_normal_right' IsPGroup.to_sup_of_normal_right'ₓ'. -/
theorem to_sup_of_normal_right' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : H ≤ K.normalizer) : IsPGroup p (H ⊔ K : Subgroup G) :=
  let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup K.normalizer => IsPGroup p H)
            (Subgroup.sup_subgroupOf_eq hHK Subgroup.le_normalizer)).mp
        hHK').of_equiv
    (Subgroup.subgroupOfEquivOfLe (sup_le hHK Subgroup.le_normalizer))
#align is_p_group.to_sup_of_normal_right' IsPGroup.to_sup_of_normal_right'

/- warning: is_p_group.to_sup_of_normal_left' -> IsPGroup.to_sup_of_normal_left' is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toHasLe.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) K (Subgroup.normalizer.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)) (Subgroup.toGroup.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) (Subgroup.toGroup.{u1} G _inst_1 K)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) K (Subgroup.normalizer.{u1} G _inst_1 H)) -> (IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K))) (Subgroup.toGroup.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K)))
Case conversion may be inaccurate. Consider using '#align is_p_group.to_sup_of_normal_left' IsPGroup.to_sup_of_normal_left'ₓ'. -/
theorem to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : K ≤ H.normalizer) : IsPGroup p (H ⊔ K : Subgroup G) :=
  (congr_arg (fun H : Subgroup G => IsPGroup p H) sup_comm).mp (to_sup_of_normal_right' hK hH hHK)
#align is_p_group.to_sup_of_normal_left' IsPGroup.to_sup_of_normal_left'

/- warning: is_p_group.coprime_card_of_ne -> IsPGroup.coprime_card_of_ne is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {G₂ : Type.{u2}} [_inst_2 : Group.{u2} G₂] (p₁ : Nat) (p₂ : Nat) [hp₁ : Fact (Nat.Prime p₁)] [hp₂ : Fact (Nat.Prime p₂)], (Ne.{1} Nat p₁ p₂) -> (forall (H₁ : Subgroup.{u1} G _inst_1) (H₂ : Subgroup.{u2} G₂ _inst_2) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H₁)] [_inst_4 : Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G₂ _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G₂ _inst_2) G₂ (Subgroup.setLike.{u2} G₂ _inst_2)) H₂)], (IsPGroup.{u1} p₁ (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H₁) (Subgroup.toGroup.{u1} G _inst_1 H₁)) -> (IsPGroup.{u2} p₂ (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G₂ _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G₂ _inst_2) G₂ (Subgroup.setLike.{u2} G₂ _inst_2)) H₂) (Subgroup.toGroup.{u2} G₂ _inst_2 H₂)) -> (Nat.coprime (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H₁) _inst_3) (Fintype.card.{u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G₂ _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G₂ _inst_2) G₂ (Subgroup.setLike.{u2} G₂ _inst_2)) H₂) _inst_4)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {G₂ : Type.{u2}} [_inst_2 : Group.{u2} G₂] (p₁ : Nat) (p₂ : Nat) [hp₁ : Fact (Nat.Prime p₁)] [hp₂ : Fact (Nat.Prime p₂)], (Ne.{1} Nat p₁ p₂) -> (forall (H₁ : Subgroup.{u1} G _inst_1) (H₂ : Subgroup.{u2} G₂ _inst_2) [_inst_3 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H₁))] [_inst_4 : Fintype.{u2} (Subtype.{succ u2} G₂ (fun (x : G₂) => Membership.mem.{u2, u2} G₂ (Subgroup.{u2} G₂ _inst_2) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G₂ _inst_2) G₂ (Subgroup.instSetLikeSubgroup.{u2} G₂ _inst_2)) x H₂))], (IsPGroup.{u1} p₁ (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H₁)) (Subgroup.toGroup.{u1} G _inst_1 H₁)) -> (IsPGroup.{u2} p₂ (Subtype.{succ u2} G₂ (fun (x : G₂) => Membership.mem.{u2, u2} G₂ (Subgroup.{u2} G₂ _inst_2) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G₂ _inst_2) G₂ (Subgroup.instSetLikeSubgroup.{u2} G₂ _inst_2)) x H₂)) (Subgroup.toGroup.{u2} G₂ _inst_2 H₂)) -> (Nat.coprime (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H₁)) _inst_3) (Fintype.card.{u2} (Subtype.{succ u2} G₂ (fun (x : G₂) => Membership.mem.{u2, u2} G₂ (Subgroup.{u2} G₂ _inst_2) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G₂ _inst_2) G₂ (Subgroup.instSetLikeSubgroup.{u2} G₂ _inst_2)) x H₂)) _inst_4)))
Case conversion may be inaccurate. Consider using '#align is_p_group.coprime_card_of_ne IsPGroup.coprime_card_of_neₓ'. -/
/-- finite p-groups with different p have coprime orders -/
theorem coprime_card_of_ne {G₂ : Type _} [Group G₂] (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime]
    [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂) (H₁ : Subgroup G) (H₂ : Subgroup G₂) [Fintype H₁]
    [Fintype H₂] (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) :
    Nat.coprime (Fintype.card H₁) (Fintype.card H₂) :=
  by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁; rw [heq₁]; clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂; rw [heq₂]; clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne
#align is_p_group.coprime_card_of_ne IsPGroup.coprime_card_of_ne

/- warning: is_p_group.disjoint_of_ne -> IsPGroup.disjoint_of_ne is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (p₁ : Nat) (p₂ : Nat) [hp₁ : Fact (Nat.Prime p₁)] [hp₂ : Fact (Nat.Prime p₂)], (Ne.{1} Nat p₁ p₂) -> (forall (H₁ : Subgroup.{u1} G _inst_1) (H₂ : Subgroup.{u1} G _inst_1), (IsPGroup.{u1} p₁ (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H₁) (Subgroup.toGroup.{u1} G _inst_1 H₁)) -> (IsPGroup.{u1} p₂ (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H₂) (Subgroup.toGroup.{u1} G _inst_1 H₂)) -> (Disjoint.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (BoundedOrder.toOrderBot.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toHasLe.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))) H₁ H₂))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (p₁ : Nat) (p₂ : Nat) [hp₁ : Fact (Nat.Prime p₁)] [hp₂ : Fact (Nat.Prime p₂)], (Ne.{1} Nat p₁ p₂) -> (forall (H₁ : Subgroup.{u1} G _inst_1) (H₂ : Subgroup.{u1} G _inst_1), (IsPGroup.{u1} p₁ (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H₁)) (Subgroup.toGroup.{u1} G _inst_1 H₁)) -> (IsPGroup.{u1} p₂ (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H₂)) (Subgroup.toGroup.{u1} G _inst_1 H₂)) -> (Disjoint.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))) (BoundedOrder.toOrderBot.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))) H₁ H₂))
Case conversion may be inaccurate. Consider using '#align is_p_group.disjoint_of_ne IsPGroup.disjoint_of_neₓ'. -/
/-- p-groups with different p are disjoint -/
theorem disjoint_of_ne (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂)
    (H₁ H₂ : Subgroup G) (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) : Disjoint H₁ H₂ :=
  by
  rw [Subgroup.disjoint_def]
  intro x hx₁ hx₂
  obtain ⟨n₁, hn₁⟩ := iff_order_of.mp hH₁ ⟨x, hx₁⟩
  obtain ⟨n₂, hn₂⟩ := iff_order_of.mp hH₂ ⟨x, hx₂⟩
  rw [← orderOf_subgroup, Subgroup.coe_mk] at hn₁ hn₂
  have : p₁ ^ n₁ = p₂ ^ n₂ := by rw [← hn₁, ← hn₂]
  rcases n₁.eq_zero_or_pos with (rfl | hn₁)
  · simpa using hn₁
  · exact absurd (eq_of_prime_pow_eq hp₁.out.prime hp₂.out.prime hn₁ this) hne
#align is_p_group.disjoint_of_ne IsPGroup.disjoint_of_ne

section P2comm

variable [Fintype G] [Fact p.Prime] {n : ℕ} (hGpn : card G = p ^ n)

include hGpn

open Subgroup

/- warning: is_p_group.card_center_eq_prime_pow -> IsPGroup.card_center_eq_prime_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Fintype.{u1} G] [_inst_3 : Fact (Nat.Prime p)] {n : Nat}, (Eq.{1} Nat (Fintype.card.{u1} G _inst_2) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n)) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (forall [_inst_4 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1))], Exists.{1} Nat (fun (k : Nat) => Exists.{0} (GT.gt.{0} Nat Nat.hasLt k (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (H : GT.gt.{0} Nat Nat.hasLt k (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Eq.{1} Nat (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) _inst_4) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p k))))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Fintype.{u1} G] [_inst_3 : Fact (Nat.Prime p)] {n : Nat}, (Eq.{1} Nat (Fintype.card.{u1} G _inst_2) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (forall [_inst_4 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Subgroup.center.{u1} G _inst_1)))], Exists.{1} Nat (fun (k : Nat) => And (GT.gt.{0} Nat instLTNat k (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Eq.{1} Nat (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Subgroup.center.{u1} G _inst_1))) _inst_4) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p k))))
Case conversion may be inaccurate. Consider using '#align is_p_group.card_center_eq_prime_pow IsPGroup.card_center_eq_prime_powₓ'. -/
/-- The cardinality of the `center` of a `p`-group is `p ^ k` where `k` is positive. -/
theorem card_center_eq_prime_pow (hn : 0 < n) [Fintype (center G)] :
    ∃ k > 0, card (center G) = p ^ k :=
  by
  have hcG := to_subgroup (of_card hGpn) (center G)
  rcases iff_card.1 hcG with ⟨k, hk⟩
  haveI : Nontrivial G := (nontrivial_iff_card <| of_card hGpn).2 ⟨n, hn, hGpn⟩
  exact (nontrivial_iff_card hcG).mp (center_nontrivial (of_card hGpn))
#align is_p_group.card_center_eq_prime_pow IsPGroup.card_center_eq_prime_pow

omit hGpn

#print IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq /-
/-- The quotient by the center of a group of cardinality `p ^ 2` is cyclic. -/
theorem cyclic_center_quotient_of_card_eq_prime_sq (hG : card G = p ^ 2) :
    IsCyclic (G ⧸ center G) := by
  classical
    rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩
    rw [card_eq_card_quotient_mul_card_subgroup (center G), mul_comm, hk] at hG
    have hk2 := (Nat.pow_dvd_pow_iff_le_right (Fact.out p.prime).one_lt).1 ⟨_, hG.symm⟩
    interval_cases
    · rw [sq, pow_one, mul_right_inj' (Fact.out p.prime).NeZero] at hG
      exact isCyclic_of_prime_card hG
    ·
      exact
        @isCyclic_of_subsingleton _ _
          ⟨Fintype.card_le_one_iff.1
              (mul_right_injective₀ (pow_ne_zero 2 (NeZero.ne p))
                  (hG.trans (mul_one (p ^ 2)).symm)).le⟩
#align is_p_group.cyclic_center_quotient_of_card_eq_prime_sq IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq
-/

#print IsPGroup.commGroupOfCardEqPrimeSq /-
/-- A group of order `p ^ 2` is commutative. See also `is_p_group.commutative_of_card_eq_prime_sq`
for just the proof that `∀ a b, a * b = b * a` -/
def commGroupOfCardEqPrimeSq (hG : card G = p ^ 2) : CommGroup G :=
  @commGroupOfCycleCenterQuotient _ _ _ _ (cyclic_center_quotient_of_card_eq_prime_sq hG) _
    (QuotientGroup.ker_mk' (center G)).le
#align is_p_group.comm_group_of_card_eq_prime_sq IsPGroup.commGroupOfCardEqPrimeSq
-/

/- warning: is_p_group.commutative_of_card_eq_prime_sq -> IsPGroup.commutative_of_card_eq_prime_sq is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Fintype.{u1} G] [_inst_3 : Fact (Nat.Prime p)], (Eq.{1} Nat (Fintype.card.{u1} G _inst_2) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> (forall (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a))
but is expected to have type
  forall {p : Nat} {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Fintype.{u1} G] [_inst_3 : Fact (Nat.Prime p)], (Eq.{1} Nat (Fintype.card.{u1} G _inst_2) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) -> (forall (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align is_p_group.commutative_of_card_eq_prime_sq IsPGroup.commutative_of_card_eq_prime_sqₓ'. -/
/-- A group of order `p ^ 2` is commutative. See also `is_p_group.comm_group_of_card_eq_prime_sq`
for the `comm_group` instance. -/
theorem commutative_of_card_eq_prime_sq (hG : card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
  (commGroupOfCardEqPrimeSq hG).mul_comm
#align is_p_group.commutative_of_card_eq_prime_sq IsPGroup.commutative_of_card_eq_prime_sq

end P2comm

end IsPGroup

