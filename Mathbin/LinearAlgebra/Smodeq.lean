/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module linear_algebra.smodeq
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Eval
import Mathbin.RingTheory.Ideal.Quotient

/-!
# modular equivalence for submodule

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Submodule

open Polynomial

variable {R : Type _} [Ring R]

variable {M : Type _} [AddCommGroup M] [Module R M] (U U₁ U₂ : Submodule R M)

variable {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}

variable {N : Type _} [AddCommGroup N] [Module R N] (V V₁ V₂ : Submodule R N)

#print SModEq /-
/-- A predicate saying two elements of a module are equivalent modulo a submodule. -/
def SModEq (x y : M) : Prop :=
  (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y
#align smodeq SModEq
-/

-- mathport name: «expr ≡ [SMOD ]»
notation:50 x " ≡ " y " [SMOD " N "]" => SModEq N x y

variable {U U₁ U₂}

/- warning: smodeq.def -> SModEq.def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M} {y : M}, Iff (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x y) (Eq.{succ u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) U) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 U x) (Submodule.Quotient.mk.{u1, u2} R M _inst_1 _inst_2 _inst_3 U y))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} {x : M} {y : M}, Iff (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x y) (Eq.{succ u1} (HasQuotient.Quotient.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.hasQuotient.{u2, u1} R M _inst_1 _inst_2 _inst_3) U) (Submodule.Quotient.mk.{u2, u1} R M _inst_1 _inst_2 _inst_3 U x) (Submodule.Quotient.mk.{u2, u1} R M _inst_1 _inst_2 _inst_3 U y))
Case conversion may be inaccurate. Consider using '#align smodeq.def SModEq.defₓ'. -/
protected theorem SModEq.def :
    x ≡ y [SMOD U] ↔ (Submodule.Quotient.mk x : M ⧸ U) = Submodule.Quotient.mk y :=
  Iff.rfl
#align smodeq.def SModEq.def

namespace SModEq

/- warning: smodeq.sub_mem -> SModEq.sub_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M} {y : M}, Iff (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x y) (Membership.Mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))) x y) U)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} {x : M} {y : M}, Iff (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x y) (Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) M (Submodule.setLike.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)) (HSub.hSub.{u1, u1, u1} M M M (instHSub.{u1} M (SubNegMonoid.toSub.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_2)))) x y) U)
Case conversion may be inaccurate. Consider using '#align smodeq.sub_mem SModEq.sub_memₓ'. -/
theorem sub_mem : x ≡ y [SMOD U] ↔ x - y ∈ U := by rw [SModEq.def, Submodule.Quotient.eq]
#align smodeq.sub_mem SModEq.sub_mem

/- warning: smodeq.top -> SModEq.top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {x : M} {y : M}, SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasTop.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) x y
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {x : M} {y : M}, SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 (Top.top.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.instTopSubmodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)) x y
Case conversion may be inaccurate. Consider using '#align smodeq.top SModEq.topₓ'. -/
@[simp]
theorem top : x ≡ y [SMOD (⊤ : Submodule R M)] :=
  (Submodule.Quotient.eq ⊤).2 mem_top
#align smodeq.top SModEq.top

/- warning: smodeq.bot -> SModEq.bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {x : M} {y : M}, Iff (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 (Bot.bot.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasBot.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) x y) (Eq.{succ u2} M x y)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {x : M} {y : M}, Iff (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 (Bot.bot.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (Submodule.instBotSubmodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)) x y) (Eq.{succ u1} M x y)
Case conversion may be inaccurate. Consider using '#align smodeq.bot SModEq.botₓ'. -/
@[simp]
theorem bot : x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y := by
  rw [SModEq.def, Submodule.Quotient.eq, mem_bot, sub_eq_zero]
#align smodeq.bot SModEq.bot

/- warning: smodeq.mono -> SModEq.mono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U₁ : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {U₂ : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M} {y : M}, (LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toHasLe.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.partialOrder.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) U₁ U₂) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U₁ x y) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U₂ x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U₁ : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {U₂ : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M} {y : M}, (LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) U₁ U₂) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U₁ x y) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U₂ x y)
Case conversion may be inaccurate. Consider using '#align smodeq.mono SModEq.monoₓ'. -/
@[mono]
theorem mono (HU : U₁ ≤ U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
  (Submodule.Quotient.eq U₂).2 <| HU <| (Submodule.Quotient.eq U₁).1 hxy
#align smodeq.mono SModEq.mono

/- warning: smodeq.refl -> SModEq.refl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} (x : M), SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x x
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} (x : M), SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x x
Case conversion may be inaccurate. Consider using '#align smodeq.refl SModEq.reflₓ'. -/
@[refl]
protected theorem refl (x : M) : x ≡ x [SMOD U] :=
  @rfl _ _
#align smodeq.refl SModEq.refl

/- warning: smodeq.rfl -> SModEq.rfl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M}, SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x x
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} {x : M}, SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x x
Case conversion may be inaccurate. Consider using '#align smodeq.rfl SModEq.rflₓ'. -/
protected theorem rfl : x ≡ x [SMOD U] :=
  SModEq.refl _
#align smodeq.rfl SModEq.rfl

instance : IsRefl _ (SModEq U) :=
  ⟨SModEq.refl⟩

/- warning: smodeq.symm -> SModEq.symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M} {y : M}, (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x y) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U y x)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} {x : M} {y : M}, (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x y) -> (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U y x)
Case conversion may be inaccurate. Consider using '#align smodeq.symm SModEq.symmₓ'. -/
@[symm]
theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
  hxy.symm
#align smodeq.symm SModEq.symm

/- warning: smodeq.trans -> SModEq.trans is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M} {y : M} {z : M}, (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x y) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U y z) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x z)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} {x : M} {y : M} {z : M}, (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x y) -> (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U y z) -> (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x z)
Case conversion may be inaccurate. Consider using '#align smodeq.trans SModEq.transₓ'. -/
@[trans]
theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
  hxy.trans hyz
#align smodeq.trans SModEq.trans

/- warning: smodeq.add -> SModEq.add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x₁ : M} {x₂ : M} {y₁ : M} {y₂ : M}, (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x₁ y₁) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x₂ y₂) -> (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))) x₁ x₂) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))) y₁ y₂))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} {x₁ : M} {x₂ : M} {y₁ : M} {y₂ : M}, (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x₁ y₁) -> (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x₂ y₂) -> (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_2)))))) x₁ x₂) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_2)))))) y₁ y₂))
Case conversion may be inaccurate. Consider using '#align smodeq.add SModEq.addₓ'. -/
theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] :=
  by
  rw [SModEq.def] at hxy₁ hxy₂⊢
  simp_rw [quotient.mk_add, hxy₁, hxy₂]
#align smodeq.add SModEq.add

/- warning: smodeq.smul -> SModEq.smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M} {y : M}, (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x y) -> (forall (c : R), SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U (SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) c x) (SMul.smul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)))) (Module.toMulActionWithZero.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) c y))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} {x : M} {y : M}, (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x y) -> (forall (c : R), SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U (HSMul.hSMul.{u2, u1, u1} R M M (instHSMul.{u2, u1} R M (SMulZeroClass.toSMul.{u2, u1} R M (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (SubtractionCommMonoid.toSubtractionMonoid.{u1} M (AddCommGroup.toDivisionAddCommMonoid.{u1} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R M (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (SubtractionCommMonoid.toSubtractionMonoid.{u1} M (AddCommGroup.toDivisionAddCommMonoid.{u1} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (SubtractionCommMonoid.toSubtractionMonoid.{u1} M (AddCommGroup.toDivisionAddCommMonoid.{u1} M _inst_2))))) (Module.toMulActionWithZero.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))))) c x) (HSMul.hSMul.{u2, u1, u1} R M M (instHSMul.{u2, u1} R M (SMulZeroClass.toSMul.{u2, u1} R M (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (SubtractionCommMonoid.toSubtractionMonoid.{u1} M (AddCommGroup.toDivisionAddCommMonoid.{u1} M _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R M (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (SubtractionCommMonoid.toSubtractionMonoid.{u1} M (AddCommGroup.toDivisionAddCommMonoid.{u1} M _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (SubtractionCommMonoid.toSubtractionMonoid.{u1} M (AddCommGroup.toDivisionAddCommMonoid.{u1} M _inst_2))))) (Module.toMulActionWithZero.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3))))) c y))
Case conversion may be inaccurate. Consider using '#align smodeq.smul SModEq.smulₓ'. -/
theorem smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U] :=
  by
  rw [SModEq.def] at hxy⊢
  simp_rw [quotient.mk_smul, hxy]
#align smodeq.smul SModEq.smul

/- warning: smodeq.zero -> SModEq.zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {x : M}, Iff (SModEq.{u1, u2} R _inst_1 M _inst_2 _inst_3 U x (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))))))) (Membership.Mem.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) x U)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3} {x : M}, Iff (SModEq.{u2, u1} R _inst_1 M _inst_2 _inst_3 U x (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (NegZeroClass.toZero.{u1} M (SubNegZeroMonoid.toNegZeroClass.{u1} M (SubtractionMonoid.toSubNegZeroMonoid.{u1} M (SubtractionCommMonoid.toSubtractionMonoid.{u1} M (AddCommGroup.toDivisionAddCommMonoid.{u1} M _inst_2)))))))) (Membership.mem.{u1, u1} M (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) M (Submodule.setLike.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3)) x U)
Case conversion may be inaccurate. Consider using '#align smodeq.zero SModEq.zeroₓ'. -/
theorem zero : x ≡ 0 [SMOD U] ↔ x ∈ U := by rw [SModEq.def, Submodule.Quotient.eq, sub_zero]
#align smodeq.zero SModEq.zero

/- warning: smodeq.map -> SModEq.map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align smodeq.map SModEq.mapₓ'. -/
theorem map (hxy : x ≡ y [SMOD U]) (f : M →ₗ[R] N) : f x ≡ f y [SMOD U.map f] :=
  (Submodule.Quotient.eq _).2 <| f.map_sub x y ▸ mem_map_of_mem <| (Submodule.Quotient.eq _).1 hxy
#align smodeq.map SModEq.map

/- warning: smodeq.comap -> SModEq.comap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align smodeq.comap SModEq.comapₓ'. -/
theorem comap {f : M →ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f] :=
  (Submodule.Quotient.eq _).2 <|
    show f (x - y) ∈ V from (f.map_sub x y).symm ▸ (Submodule.Quotient.eq _).1 hxy
#align smodeq.comap SModEq.comap

#print SModEq.eval /-
theorem eval {R : Type _} [CommRing R] {I : Ideal R} {x y : R} (h : x ≡ y [SMOD I]) (f : R[X]) :
    f.eval x ≡ f.eval y [SMOD I] := by
  rw [SModEq.def] at h⊢
  show Ideal.Quotient.mk I (f.eval x) = Ideal.Quotient.mk I (f.eval y)
  change Ideal.Quotient.mk I x = Ideal.Quotient.mk I y at h
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, h]
#align smodeq.eval SModEq.eval
-/

end SModEq

