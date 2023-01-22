/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module group_theory.group_action.support
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Smul

/-!
# Support of an element under an action action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given an action of a group `G` on a type `α`, we say that a set `s : set α` supports an element
`a : α` if, for all `g` that fix `s` pointwise, `g` fixes `a`.

This is crucial in Fourier-Motzkin constructions.
-/


open Pointwise

variable {G H α β : Type _}

namespace MulAction

section SMul

variable (G) [SMul G α] [SMul G β]

#print MulAction.Supports /-
/-- A set `s` supports `b` if `g • b = b` whenever `g • a = a` for all `a ∈ s`. -/
@[to_additive "A set `s` supports `b` if `g +ᵥ b = b` whenever `g +ᵥ a = a` for all `a ∈ s`."]
def Supports (s : Set α) (b : β) :=
  ∀ g : G, (∀ ⦃a⦄, a ∈ s → g • a = a) → g • b = b
#align mul_action.supports MulAction.Supports
#align add_action.supports AddAction.Supports
-/

variable {s t : Set α} {a : α} {b : β}

#print MulAction.supports_of_mem /-
@[to_additive]
theorem supports_of_mem (ha : a ∈ s) : Supports G s a := fun g h => h ha
#align mul_action.supports_of_mem MulAction.supports_of_mem
#align add_action.supports_of_mem AddAction.supports_of_mem
-/

variable {G}

/- warning: mul_action.supports.mono -> MulAction.Supports.mono is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} G α] [_inst_2 : SMul.{u1, u3} G β] {s : Set.{u2} α} {t : Set.{u2} α} {b : β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) s t) -> (MulAction.Supports.{u1, u2, u3} G α β _inst_1 _inst_2 s b) -> (MulAction.Supports.{u1, u2, u3} G α β _inst_1 _inst_2 t b)
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u3} G α] [_inst_2 : SMul.{u2, u1} G β] {s : Set.{u3} α} {t : Set.{u3} α} {b : β}, (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) s t) -> (MulAction.Supports.{u2, u3, u1} G α β _inst_1 _inst_2 s b) -> (MulAction.Supports.{u2, u3, u1} G α β _inst_1 _inst_2 t b)
Case conversion may be inaccurate. Consider using '#align mul_action.supports.mono MulAction.Supports.monoₓ'. -/
@[to_additive]
theorem Supports.mono (h : s ⊆ t) (hs : Supports G s b) : Supports G t b := fun g hg =>
  hs _ fun a ha => hg <| h ha
#align mul_action.supports.mono MulAction.Supports.mono
#align add_action.supports.mono AddAction.Supports.mono

end SMul

variable [Group H] [SMul G α] [SMul G β] [MulAction H α] [SMul H β] [SMulCommClass G H β]
  [SMulCommClass G H α] {s t : Set α} {b : β}

/- warning: mul_action.supports.smul -> MulAction.Supports.smul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Group.{u2} H] [_inst_2 : SMul.{u1, u3} G α] [_inst_3 : SMul.{u1, u4} G β] [_inst_4 : MulAction.{u2, u3} H α (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_1))] [_inst_5 : SMul.{u2, u4} H β] [_inst_6 : SMulCommClass.{u1, u2, u4} G H β _inst_3 _inst_5] [_inst_7 : SMulCommClass.{u1, u2, u3} G H α _inst_2 (MulAction.toHasSmul.{u2, u3} H α (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_1)) _inst_4)] {s : Set.{u3} α} {b : β} (g : H), (MulAction.Supports.{u1, u3, u4} G α β _inst_2 _inst_3 s b) -> (MulAction.Supports.{u1, u3, u4} G α β _inst_2 _inst_3 (SMul.smul.{u2, u3} H (Set.{u3} α) (Set.smulSet.{u2, u3} H α (MulAction.toHasSmul.{u2, u3} H α (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_1)) _inst_4)) g s) (SMul.smul.{u2, u4} H β _inst_5 g b))
but is expected to have type
  forall {G : Type.{u4}} {H : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u1} H] [_inst_2 : SMul.{u4, u3} G α] [_inst_3 : SMul.{u4, u2} G β] [_inst_4 : MulAction.{u1, u3} H α (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_1))] [_inst_5 : SMul.{u1, u2} H β] [_inst_6 : SMulCommClass.{u4, u1, u2} G H β _inst_3 _inst_5] [_inst_7 : SMulCommClass.{u4, u1, u3} G H α _inst_2 (MulAction.toSMul.{u1, u3} H α (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_1)) _inst_4)] {s : Set.{u3} α} {b : β} (g : H), (MulAction.Supports.{u4, u3, u2} G α β _inst_2 _inst_3 s b) -> (MulAction.Supports.{u4, u3, u2} G α β _inst_2 _inst_3 (HSMul.hSMul.{u1, u3, u3} H (Set.{u3} α) (Set.{u3} α) (instHSMul.{u1, u3} H (Set.{u3} α) (Set.smulSet.{u1, u3} H α (MulAction.toSMul.{u1, u3} H α (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_1)) _inst_4))) g s) (HSMul.hSMul.{u1, u2, u2} H β β (instHSMul.{u1, u2} H β _inst_5) g b))
Case conversion may be inaccurate. Consider using '#align mul_action.supports.smul MulAction.Supports.smulₓ'. -/
-- TODO: This should work without `smul_comm_class`
@[to_additive]
theorem Supports.smul (g : H) (h : Supports G s b) : Supports G (g • s) (g • b) :=
  by
  rintro g' hg'
  rw [smul_comm, h]
  rintro a ha
  have := Set.ball_image_iff.1 hg' a ha
  rwa [smul_comm, smul_left_cancel_iff] at this
#align mul_action.supports.smul MulAction.Supports.smul
#align add_action.supports.vadd AddAction.Supports.vadd

end MulAction

