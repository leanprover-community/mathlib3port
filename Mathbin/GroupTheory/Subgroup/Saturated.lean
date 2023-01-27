/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module group_theory.subgroup.saturated
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Saturated subgroups

## Tags
subgroup, subgroups

-/


namespace Subgroup

variable {G : Type _} [Group G]

#print Subgroup.Saturated /-
/-- A subgroup `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with `g^n ∈ H`
we have `n = 0` or `g ∈ H`. -/
@[to_additive
      "An additive subgroup `H` of `G` is *saturated* if\nfor all `n : ℕ` and `g : G` with `n•g ∈ H` we have `n = 0` or `g ∈ H`."]
def Saturated (H : Subgroup G) : Prop :=
  ∀ ⦃n g⦄, g ^ n ∈ H → n = 0 ∨ g ∈ H
#align subgroup.saturated Subgroup.Saturated
#align add_subgroup.saturated AddSubgroup.Saturated
-/

/- warning: subgroup.saturated_iff_npow -> Subgroup.saturated_iff_npow is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Subgroup.Saturated.{u1} G _inst_1 H) (forall (n : Nat) (g : G), (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) g n) H) -> (Or (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) g H)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Subgroup.Saturated.{u1} G _inst_1 H) (forall (n : Nat) (g : G), (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) g n) H) -> (Or (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) g H)))
Case conversion may be inaccurate. Consider using '#align subgroup.saturated_iff_npow Subgroup.saturated_iff_npowₓ'. -/
@[to_additive]
theorem saturated_iff_npow {H : Subgroup G} :
    Saturated H ↔ ∀ (n : ℕ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H :=
  Iff.rfl
#align subgroup.saturated_iff_npow Subgroup.saturated_iff_npow
#align add_subgroup.saturated_iff_nsmul AddSubgroup.saturated_iff_nsmul

/- warning: subgroup.saturated_iff_zpow -> Subgroup.saturated_iff_zpow is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Subgroup.Saturated.{u1} G _inst_1 H) (forall (n : Int) (g : G), (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) g n) H) -> (Or (Eq.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) g H)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Subgroup.Saturated.{u1} G _inst_1 H) (forall (n : Int) (g : G), (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) g n) H) -> (Or (Eq.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) g H)))
Case conversion may be inaccurate. Consider using '#align subgroup.saturated_iff_zpow Subgroup.saturated_iff_zpowₓ'. -/
@[to_additive]
theorem saturated_iff_zpow {H : Subgroup G} :
    Saturated H ↔ ∀ (n : ℤ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H :=
  by
  constructor
  · rintro hH ⟨n⟩ g hgn
    · simp only [Int.coe_nat_eq_zero, Int.ofNat_eq_coe, zpow_ofNat] at hgn⊢
      exact hH hgn
    · suffices g ^ (n + 1) ∈ H by
        refine' (hH this).imp _ id
        simp only [IsEmpty.forall_iff, Nat.succ_ne_zero]
      simpa only [inv_mem_iff, zpow_negSucc] using hgn
  · intro h n g hgn
    specialize h n g
    simp only [Int.coe_nat_eq_zero, zpow_ofNat] at h
    apply h hgn
#align subgroup.saturated_iff_zpow Subgroup.saturated_iff_zpow
#align add_subgroup.saturated_iff_zsmul AddSubgroup.saturated_iff_zsmul

end Subgroup

namespace AddSubgroup

/- warning: add_subgroup.ker_saturated -> AddSubgroup.ker_saturated is a dubious translation:
lean 3 declaration is
  forall {A₁ : Type.{u1}} {A₂ : Type.{u2}} [_inst_1 : AddCommGroup.{u1} A₁] [_inst_2 : AddCommGroup.{u2} A₂] [_inst_3 : NoZeroSMulDivisors.{0, u2} Nat A₂ Nat.hasZero (AddZeroClass.toHasZero.{u2} A₂ (AddMonoid.toAddZeroClass.{u2} A₂ (SubNegMonoid.toAddMonoid.{u2} A₂ (AddGroup.toSubNegMonoid.{u2} A₂ (AddCommGroup.toAddGroup.{u2} A₂ _inst_2))))) (AddMonoid.SMul.{u2} A₂ (SubNegMonoid.toAddMonoid.{u2} A₂ (AddGroup.toSubNegMonoid.{u2} A₂ (AddCommGroup.toAddGroup.{u2} A₂ _inst_2))))] (f : AddMonoidHom.{u1, u2} A₁ A₂ (AddMonoid.toAddZeroClass.{u1} A₁ (SubNegMonoid.toAddMonoid.{u1} A₁ (AddGroup.toSubNegMonoid.{u1} A₁ (AddCommGroup.toAddGroup.{u1} A₁ _inst_1)))) (AddMonoid.toAddZeroClass.{u2} A₂ (SubNegMonoid.toAddMonoid.{u2} A₂ (AddGroup.toSubNegMonoid.{u2} A₂ (AddCommGroup.toAddGroup.{u2} A₂ _inst_2))))), AddSubgroup.Saturated.{u1} A₁ (AddCommGroup.toAddGroup.{u1} A₁ _inst_1) (AddMonoidHom.ker.{u1, u2} A₁ (AddCommGroup.toAddGroup.{u1} A₁ _inst_1) A₂ (AddMonoid.toAddZeroClass.{u2} A₂ (SubNegMonoid.toAddMonoid.{u2} A₂ (AddGroup.toSubNegMonoid.{u2} A₂ (AddCommGroup.toAddGroup.{u2} A₂ _inst_2)))) f)
but is expected to have type
  forall {A₁ : Type.{u2}} {A₂ : Type.{u1}} [_inst_1 : AddCommGroup.{u2} A₁] [_inst_2 : AddCommGroup.{u1} A₂] [_inst_3 : NoZeroSMulDivisors.{0, u1} Nat A₂ (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (NegZeroClass.toZero.{u1} A₂ (SubNegZeroMonoid.toNegZeroClass.{u1} A₂ (SubtractionMonoid.toSubNegZeroMonoid.{u1} A₂ (SubtractionCommMonoid.toSubtractionMonoid.{u1} A₂ (AddCommGroup.toDivisionAddCommMonoid.{u1} A₂ _inst_2))))) (AddMonoid.SMul.{u1} A₂ (SubNegMonoid.toAddMonoid.{u1} A₂ (AddGroup.toSubNegMonoid.{u1} A₂ (AddCommGroup.toAddGroup.{u1} A₂ _inst_2))))] (f : AddMonoidHom.{u2, u1} A₁ A₂ (AddMonoid.toAddZeroClass.{u2} A₁ (SubNegMonoid.toAddMonoid.{u2} A₁ (AddGroup.toSubNegMonoid.{u2} A₁ (AddCommGroup.toAddGroup.{u2} A₁ _inst_1)))) (AddMonoid.toAddZeroClass.{u1} A₂ (SubNegMonoid.toAddMonoid.{u1} A₂ (AddGroup.toSubNegMonoid.{u1} A₂ (AddCommGroup.toAddGroup.{u1} A₂ _inst_2))))), AddSubgroup.Saturated.{u2} A₁ (AddCommGroup.toAddGroup.{u2} A₁ _inst_1) (AddMonoidHom.ker.{u2, u1} A₁ (AddCommGroup.toAddGroup.{u2} A₁ _inst_1) A₂ (AddMonoid.toAddZeroClass.{u1} A₂ (SubNegMonoid.toAddMonoid.{u1} A₂ (AddGroup.toSubNegMonoid.{u1} A₂ (AddCommGroup.toAddGroup.{u1} A₂ _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align add_subgroup.ker_saturated AddSubgroup.ker_saturatedₓ'. -/
theorem ker_saturated {A₁ A₂ : Type _} [AddCommGroup A₁] [AddCommGroup A₂] [NoZeroSMulDivisors ℕ A₂]
    (f : A₁ →+ A₂) : f.ker.Saturated := by
  intro n g hg
  simpa only [f.mem_ker, nsmul_eq_smul, f.map_nsmul, smul_eq_zero] using hg
#align add_subgroup.ker_saturated AddSubgroup.ker_saturated

end AddSubgroup

