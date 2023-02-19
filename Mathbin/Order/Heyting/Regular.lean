/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.heyting.regular
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.GaloisConnection

/-!
# Heyting regular elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines Heyting regular elements, elements of an Heyting algebra that are their own double
complement, and proves that they form a boolean algebra.

From a logic standpoint, this means that we can perform classical logic within intuitionistic logic
by simply double-negating all propositions. This is practical for synthetic computability theory.

## Main declarations

* `is_regular`: `a` is Heyting-regular if `aᶜᶜ = a`.
* `regular`: The subtype of Heyting-regular elements.
* `regular.boolean_algebra`: Heyting-regular elements form a boolean algebra.

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/


open Function

variable {α : Type _}

namespace Heyting

section HasCompl

variable [HasCompl α] {a : α}

#print Heyting.IsRegular /-
/-- An element of an Heyting algebra is regular if its double complement is itself. -/
def IsRegular (a : α) : Prop :=
  aᶜᶜ = a
#align heyting.is_regular Heyting.IsRegular
-/

#print Heyting.IsRegular.eq /-
protected theorem IsRegular.eq : IsRegular a → aᶜᶜ = a :=
  id
#align heyting.is_regular.eq Heyting.IsRegular.eq
-/

#print Heyting.IsRegular.decidablePred /-
instance IsRegular.decidablePred [DecidableEq α] : @DecidablePred α IsRegular := fun _ =>
  ‹DecidableEq α› _ _
#align heyting.is_regular.decidable_pred Heyting.IsRegular.decidablePred
-/

end HasCompl

section HeytingAlgebra

variable [HeytingAlgebra α] {a b : α}

/- warning: heyting.is_regular_bot -> Heyting.isRegular_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align heyting.is_regular_bot Heyting.isRegular_botₓ'. -/
theorem isRegular_bot : IsRegular (⊥ : α) := by rw [IsRegular, compl_bot, compl_top]
#align heyting.is_regular_bot Heyting.isRegular_bot

/- warning: heyting.is_regular_top -> Heyting.isRegular_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align heyting.is_regular_top Heyting.isRegular_topₓ'. -/
theorem isRegular_top : IsRegular (⊤ : α) := by rw [IsRegular, compl_top, compl_bot]
#align heyting.is_regular_top Heyting.isRegular_top

#print Heyting.IsRegular.inf /-
theorem IsRegular.inf (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⊓ b) := by
  rw [IsRegular, compl_compl_inf_distrib, ha.eq, hb.eq]
#align heyting.is_regular.inf Heyting.IsRegular.inf
-/

/- warning: heyting.is_regular.himp -> Heyting.IsRegular.himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, (Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) -> (Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) b) -> (Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] {a : α} {b : α}, (Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) a) -> (Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) b) -> (Heyting.IsRegular.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align heyting.is_regular.himp Heyting.IsRegular.himpₓ'. -/
theorem IsRegular.himp (ha : IsRegular a) (hb : IsRegular b) : IsRegular (a ⇨ b) := by
  rw [IsRegular, compl_compl_himp_distrib, ha.eq, hb.eq]
#align heyting.is_regular.himp Heyting.IsRegular.himp

#print Heyting.isRegular_compl /-
theorem isRegular_compl (a : α) : IsRegular (aᶜ) :=
  compl_compl_compl _
#align heyting.is_regular_compl Heyting.isRegular_compl
-/

#print Heyting.IsRegular.disjoint_compl_left_iff /-
protected theorem IsRegular.disjoint_compl_left_iff (ha : IsRegular a) : Disjoint (aᶜ) b ↔ b ≤ a :=
  by rw [← le_compl_iff_disjoint_left, ha.eq]
#align heyting.is_regular.disjoint_compl_left_iff Heyting.IsRegular.disjoint_compl_left_iff
-/

#print Heyting.IsRegular.disjoint_compl_right_iff /-
protected theorem IsRegular.disjoint_compl_right_iff (hb : IsRegular b) : Disjoint a (bᶜ) ↔ a ≤ b :=
  by rw [← le_compl_iff_disjoint_right, hb.eq]
#align heyting.is_regular.disjoint_compl_right_iff Heyting.IsRegular.disjoint_compl_right_iff
-/

#print BooleanAlgebra.ofRegular /-
-- See note [reducible non-instances]
/-- A Heyting algebra with regular excluded middle is a boolean algebra. -/
@[reducible]
def BooleanAlgebra.ofRegular (h : ∀ a : α, IsRegular (a ⊔ aᶜ)) : BooleanAlgebra α :=
  have : ∀ a : α, IsCompl a (aᶜ) := fun a =>
    ⟨disjoint_compl_right,
      codisjoint_iff.2 <| by erw [← (h a).Eq, compl_sup, inf_compl_eq_bot, compl_bot]⟩
  { ‹HeytingAlgebra α›,
    GeneralizedHeytingAlgebra.toDistribLattice with
    himp_eq := fun a b =>
      eq_of_forall_le_iff fun c => le_himp_iff.trans (this _).le_sup_right_iff_inf_left_le.symm
    inf_compl_le_bot := fun a => (this _).1.le_bot
    top_le_sup_compl := fun a => (this _).2.top_le }
#align boolean_algebra.of_regular BooleanAlgebra.ofRegular
-/

variable (α)

#print Heyting.Regular /-
/-- The boolean algebra of Heyting regular elements. -/
def Regular : Type _ :=
  { a : α // IsRegular a }
#align heyting.regular Heyting.Regular
-/

variable {α}

namespace Regular

instance : Coe (Regular α) α :=
  coeSubtype

#print Heyting.Regular.coe_injective /-
theorem coe_injective : Injective (coe : Regular α → α) :=
  Subtype.coe_injective
#align heyting.regular.coe_injective Heyting.Regular.coe_injective
-/

#print Heyting.Regular.coe_inj /-
@[simp]
theorem coe_inj {a b : Regular α} : (a : α) = b ↔ a = b :=
  Subtype.coe_inj
#align heyting.regular.coe_inj Heyting.Regular.coe_inj
-/

instance : Top (Regular α) :=
  ⟨⟨⊤, isRegular_top⟩⟩

instance : Bot (Regular α) :=
  ⟨⟨⊥, isRegular_bot⟩⟩

instance : HasInf (Regular α) :=
  ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

instance : HImp (Regular α) :=
  ⟨fun a b => ⟨a ⇨ b, a.2.himp b.2⟩⟩

instance : HasCompl (Regular α) :=
  ⟨fun a => ⟨aᶜ, isRegular_compl _⟩⟩

/- warning: heyting.regular.coe_top -> Heyting.Regular.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Heyting.Regular.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (Heyting.Regular.hasCoe.{u1} α _inst_1)))) (Top.top.{u1} (Heyting.Regular.{u1} α _inst_1) (Heyting.Regular.hasTop.{u1} α _inst_1))) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toHasTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Eq.{succ u1} α (Heyting.Regular.val.{u1} α _inst_1 (Top.top.{u1} (Heyting.Regular.{u1} α _inst_1) (Heyting.Regular.top.{u1} α _inst_1))) (Top.top.{u1} α (GeneralizedHeytingAlgebra.toTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align heyting.regular.coe_top Heyting.Regular.coe_topₓ'. -/
@[simp, norm_cast]
theorem coe_top : ((⊤ : Regular α) : α) = ⊤ :=
  rfl
#align heyting.regular.coe_top Heyting.Regular.coe_top

/- warning: heyting.regular.coe_bot -> Heyting.Regular.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Heyting.Regular.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (Heyting.Regular.hasCoe.{u1} α _inst_1)))) (Bot.bot.{u1} (Heyting.Regular.{u1} α _inst_1) (Heyting.Regular.hasBot.{u1} α _inst_1))) (Bot.bot.{u1} α (HeytingAlgebra.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α], Eq.{succ u1} α (Heyting.Regular.val.{u1} α _inst_1 (Bot.bot.{u1} (Heyting.Regular.{u1} α _inst_1) (Heyting.Regular.bot.{u1} α _inst_1))) (Bot.bot.{u1} α (HeytingAlgebra.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align heyting.regular.coe_bot Heyting.Regular.coe_botₓ'. -/
@[simp, norm_cast]
theorem coe_bot : ((⊥ : Regular α) : α) = ⊥ :=
  rfl
#align heyting.regular.coe_bot Heyting.Regular.coe_bot

#print Heyting.Regular.coe_inf /-
@[simp, norm_cast]
theorem coe_inf (a b : Regular α) : (↑(a ⊓ b) : α) = a ⊓ b :=
  rfl
#align heyting.regular.coe_inf Heyting.Regular.coe_inf
-/

/- warning: heyting.regular.coe_himp -> Heyting.Regular.coe_himp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : Heyting.Regular.{u1} α _inst_1) (b : Heyting.Regular.{u1} α _inst_1), Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Heyting.Regular.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (Heyting.Regular.hasCoe.{u1} α _inst_1)))) (HImp.himp.{u1} (Heyting.Regular.{u1} α _inst_1) (Heyting.Regular.hasHimp.{u1} α _inst_1) a b)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHasHimp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Heyting.Regular.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (Heyting.Regular.hasCoe.{u1} α _inst_1)))) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Heyting.Regular.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (Heyting.Regular.hasCoe.{u1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : Heyting.Regular.{u1} α _inst_1) (b : Heyting.Regular.{u1} α _inst_1), Eq.{succ u1} α (Heyting.Regular.val.{u1} α _inst_1 (HImp.himp.{u1} (Heyting.Regular.{u1} α _inst_1) (Heyting.Regular.himp.{u1} α _inst_1) a b)) (HImp.himp.{u1} α (GeneralizedHeytingAlgebra.toHImp.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)) (Heyting.Regular.val.{u1} α _inst_1 a) (Heyting.Regular.val.{u1} α _inst_1 b))
Case conversion may be inaccurate. Consider using '#align heyting.regular.coe_himp Heyting.Regular.coe_himpₓ'. -/
@[simp, norm_cast]
theorem coe_himp (a b : Regular α) : (↑(a ⇨ b) : α) = a ⇨ b :=
  rfl
#align heyting.regular.coe_himp Heyting.Regular.coe_himp

#print Heyting.Regular.coe_compl /-
@[simp, norm_cast]
theorem coe_compl (a : Regular α) : (↑(aᶜ) : α) = aᶜ :=
  rfl
#align heyting.regular.coe_compl Heyting.Regular.coe_compl
-/

instance : Inhabited (Regular α) :=
  ⟨⊥⟩

instance : SemilatticeInf (Regular α) :=
  coe_injective.SemilatticeInf _ coe_inf

instance : BoundedOrder (Regular α) :=
  BoundedOrder.lift coe (fun _ _ => id) coe_top coe_bot

#print Heyting.Regular.coe_le_coe /-
@[simp, norm_cast]
theorem coe_le_coe {a b : Regular α} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl
#align heyting.regular.coe_le_coe Heyting.Regular.coe_le_coe
-/

#print Heyting.Regular.coe_lt_coe /-
@[simp, norm_cast]
theorem coe_lt_coe {a b : Regular α} : (a : α) < b ↔ a < b :=
  Iff.rfl
#align heyting.regular.coe_lt_coe Heyting.Regular.coe_lt_coe
-/

#print Heyting.Regular.toRegular /-
/-- **Regularization** of `a`. The smallest regular element greater than `a`. -/
def toRegular : α →o Regular α :=
  ⟨fun a => ⟨aᶜᶜ, isRegular_compl _⟩, fun a b h =>
    coe_le_coe.1 <| compl_le_compl <| compl_le_compl h⟩
#align heyting.regular.to_regular Heyting.Regular.toRegular
-/

#print Heyting.Regular.coe_toRegular /-
@[simp, norm_cast]
theorem coe_toRegular (a : α) : (toRegular a : α) = aᶜᶜ :=
  rfl
#align heyting.regular.coe_to_regular Heyting.Regular.coe_toRegular
-/

#print Heyting.Regular.toRegular_coe /-
@[simp]
theorem toRegular_coe (a : Regular α) : toRegular (a : α) = a :=
  coe_injective a.2
#align heyting.regular.to_regular_coe Heyting.Regular.toRegular_coe
-/

#print Heyting.Regular.gi /-
/-- The Galois insertion between `regular.to_regular` and `coe`. -/
def gi : GaloisInsertion toRegular (coe : Regular α → α)
    where
  choice a ha := ⟨a, ha.antisymm le_compl_compl⟩
  gc a b :=
    coe_le_coe.symm.trans <|
      ⟨le_compl_compl.trans, fun h => (compl_anti <| compl_anti h).trans_eq b.2⟩
  le_l_u _ := le_compl_compl
  choice_eq a ha := coe_injective <| le_compl_compl.antisymm ha
#align heyting.regular.gi Heyting.Regular.gi
-/

instance : Lattice (Regular α) :=
  gi.liftLattice

#print Heyting.Regular.coe_sup /-
@[simp, norm_cast]
theorem coe_sup (a b : Regular α) : (↑(a ⊔ b) : α) = (a ⊔ b)ᶜᶜ :=
  rfl
#align heyting.regular.coe_sup Heyting.Regular.coe_sup
-/

instance : BooleanAlgebra (Regular α) :=
  { Regular.lattice, Regular.boundedOrder, Regular.hasHimp,
    Regular.hasCompl with
    le_sup_inf := fun a b c =>
      coe_le_coe.1 <| by
        dsimp
        rw [sup_inf_left, compl_compl_inf_distrib]
    inf_compl_le_bot := fun a => coe_le_coe.1 <| disjoint_iff_inf_le.1 disjoint_compl_right
    top_le_sup_compl := fun a =>
      coe_le_coe.1 <| by
        dsimp
        rw [compl_sup, inf_compl_eq_bot, compl_bot]
        rfl
    himp_eq := fun a b =>
      coe_injective
        (by
          dsimp
          rw [compl_sup, a.prop.eq]
          refine' eq_of_forall_le_iff fun c => le_himp_iff.trans _
          rw [le_compl_iff_disjoint_right, disjoint_left_comm, b.prop.disjoint_compl_left_iff]) }

/- warning: heyting.regular.coe_sdiff -> Heyting.Regular.coe_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : Heyting.Regular.{u1} α _inst_1) (b : Heyting.Regular.{u1} α _inst_1), Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Heyting.Regular.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (Heyting.Regular.hasCoe.{u1} α _inst_1)))) (SDiff.sdiff.{u1} (Heyting.Regular.{u1} α _inst_1) (BooleanAlgebra.toHasSdiff.{u1} (Heyting.Regular.{u1} α _inst_1) (Heyting.Regular.booleanAlgebra.{u1} α _inst_1)) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Heyting.Regular.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (Heyting.Regular.hasCoe.{u1} α _inst_1)))) a) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Heyting.Regular.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Heyting.Regular.{u1} α _inst_1) α (Heyting.Regular.hasCoe.{u1} α _inst_1)))) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : HeytingAlgebra.{u1} α] (a : Heyting.Regular.{u1} α _inst_1) (b : Heyting.Regular.{u1} α _inst_1), Eq.{succ u1} α (Heyting.Regular.val.{u1} α _inst_1 (SDiff.sdiff.{u1} (Heyting.Regular.{u1} α _inst_1) (BooleanAlgebra.toSDiff.{u1} (Heyting.Regular.{u1} α _inst_1) (Heyting.Regular.instBooleanAlgebraRegular.{u1} α _inst_1)) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (GeneralizedHeytingAlgebra.toLattice.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α _inst_1))) (Heyting.Regular.val.{u1} α _inst_1 a) (HasCompl.compl.{u1} α (HeytingAlgebra.toHasCompl.{u1} α _inst_1) (Heyting.Regular.val.{u1} α _inst_1 b)))
Case conversion may be inaccurate. Consider using '#align heyting.regular.coe_sdiff Heyting.Regular.coe_sdiffₓ'. -/
@[simp, norm_cast]
theorem coe_sdiff (a b : Regular α) : (↑(a \ b) : α) = a ⊓ bᶜ :=
  rfl
#align heyting.regular.coe_sdiff Heyting.Regular.coe_sdiff

end Regular

end HeytingAlgebra

variable [BooleanAlgebra α]

#print Heyting.isRegular_of_boolean /-
theorem isRegular_of_boolean : ∀ a : α, IsRegular a :=
  compl_compl
#align heyting.is_regular_of_boolean Heyting.isRegular_of_boolean
-/

#print Heyting.isRegular_of_decidable /-
/-- A decidable proposition is intuitionistically Heyting-regular. -/
@[nolint decidable_classical]
theorem isRegular_of_decidable (p : Prop) [Decidable p] : IsRegular p :=
  propext <| Decidable.not_not_iff _
#align heyting.is_regular_of_decidable Heyting.isRegular_of_decidable
-/

end Heyting

