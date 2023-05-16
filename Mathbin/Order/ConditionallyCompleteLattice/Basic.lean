/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.basic
! leanprover-community/mathlib commit 29cb56a7b35f72758b05a30490e1f10bd62c35c1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Bounds.Basic
import Mathbin.Order.WellFounded
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Lattice

/-!
# Theory of conditionally complete lattices.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `Sup s` and `Inf s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates `bdd_above` and `bdd_below` to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of `Sup` and `Inf`
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `Inf` and `Sup` in the statements by `c`, giving `cInf` and `cSup`.
For instance, `Inf_le` is a statement in complete lattices ensuring `Inf s ≤ x`,
while `cInf_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/


open Function OrderDual Set

variable {α β γ : Type _} {ι : Sort _}

section

/-!
Extension of Sup and Inf from a preorder `α` to `with_top α` and `with_bot α`
-/


open Classical

noncomputable instance {α : Type _} [Preorder α] [SupSet α] : SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ ∈ S then ⊤ else if BddAbove (coe ⁻¹' S : Set α) then ↑(sSup (coe ⁻¹' S : Set α)) else ⊤⟩

noncomputable instance {α : Type _} [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} then ⊤ else ↑(sInf (coe ⁻¹' S : Set α))⟩

noncomputable instance {α : Type _} [SupSet α] : SupSet (WithBot α) :=
  ⟨(@WithTop.hasInf αᵒᵈ _).sInf⟩

noncomputable instance {α : Type _} [Preorder α] [InfSet α] : InfSet (WithBot α) :=
  ⟨(@WithTop.hasSup αᵒᵈ _ _).sSup⟩

#print WithTop.sSup_eq /-
theorem WithTop.sSup_eq [Preorder α] [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hs' : BddAbove (coe ⁻¹' s : Set α)) : sSup s = ↑(sSup (coe ⁻¹' s) : α) :=
  (if_neg hs).trans <| if_pos hs'
#align with_top.Sup_eq WithTop.sSup_eq
-/

#print WithTop.sInf_eq /-
theorem WithTop.sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s ⊆ {⊤}) :
    sInf s = ↑(sInf (coe ⁻¹' s) : α) :=
  if_neg hs
#align with_top.Inf_eq WithTop.sInf_eq
-/

/- warning: with_bot.Inf_eq -> WithBot.sInf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : InfSet.{u1} α] {s : Set.{u1} (WithBot.{u1} α)}, (Not (Membership.Mem.{u1, u1} (WithBot.{u1} α) (Set.{u1} (WithBot.{u1} α)) (Set.hasMem.{u1} (WithBot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) s)) -> (BddBelow.{u1} α _inst_1 (Set.preimage.{u1, u1} α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s)) -> (Eq.{succ u1} (WithBot.{u1} α) (InfSet.sInf.{u1} (WithBot.{u1} α) (WithBot.hasInf.{u1} α _inst_1 _inst_2) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (InfSet.sInf.{u1} α _inst_2 (Set.preimage.{u1, u1} α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : InfSet.{u1} α] {s : Set.{u1} (WithBot.{u1} α)}, (Not (Membership.mem.{u1, u1} (WithBot.{u1} α) (Set.{u1} (WithBot.{u1} α)) (Set.instMembershipSet.{u1} (WithBot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)) s)) -> (BddBelow.{u1} α _inst_1 (Set.preimage.{u1, u1} α (WithBot.{u1} α) (WithBot.some.{u1} α) s)) -> (Eq.{succ u1} (WithBot.{u1} α) (InfSet.sInf.{u1} (WithBot.{u1} α) (instInfSetWithBot.{u1} α _inst_1 _inst_2) s) (WithBot.some.{u1} α (InfSet.sInf.{u1} α _inst_2 (Set.preimage.{u1, u1} α (WithBot.{u1} α) (WithBot.some.{u1} α) s))))
Case conversion may be inaccurate. Consider using '#align with_bot.Inf_eq WithBot.sInf_eqₓ'. -/
theorem WithBot.sInf_eq [Preorder α] [InfSet α] {s : Set (WithBot α)} (hs : ⊥ ∉ s)
    (hs' : BddBelow (coe ⁻¹' s : Set α)) : sInf s = ↑(sInf (coe ⁻¹' s) : α) :=
  (if_neg hs).trans <| if_pos hs'
#align with_bot.Inf_eq WithBot.sInf_eq

/- warning: with_bot.Sup_eq -> WithBot.sSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] {s : Set.{u1} (WithBot.{u1} α)}, (Not (HasSubset.Subset.{u1} (Set.{u1} (WithBot.{u1} α)) (Set.hasSubset.{u1} (WithBot.{u1} α)) s (Singleton.singleton.{u1, u1} (WithBot.{u1} α) (Set.{u1} (WithBot.{u1} α)) (Set.hasSingleton.{u1} (WithBot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))))) -> (Eq.{succ u1} (WithBot.{u1} α) (SupSet.sSup.{u1} (WithBot.{u1} α) (WithBot.hasSup.{u1} α _inst_1) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (SupSet.sSup.{u1} α _inst_1 (Set.preimage.{u1, u1} α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] {s : Set.{u1} (WithBot.{u1} α)}, (Not (HasSubset.Subset.{u1} (Set.{u1} (WithBot.{u1} α)) (Set.instHasSubsetSet.{u1} (WithBot.{u1} α)) s (Singleton.singleton.{u1, u1} (WithBot.{u1} α) (Set.{u1} (WithBot.{u1} α)) (Set.instSingletonSet.{u1} (WithBot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))))) -> (Eq.{succ u1} (WithBot.{u1} α) (SupSet.sSup.{u1} (WithBot.{u1} α) (instSupSetWithBot.{u1} α _inst_1) s) (WithBot.some.{u1} α (SupSet.sSup.{u1} α _inst_1 (Set.preimage.{u1, u1} α (WithBot.{u1} α) (WithBot.some.{u1} α) s))))
Case conversion may be inaccurate. Consider using '#align with_bot.Sup_eq WithBot.sSup_eqₓ'. -/
theorem WithBot.sSup_eq [SupSet α] {s : Set (WithBot α)} (hs : ¬s ⊆ {⊥}) :
    sSup s = ↑(sSup (coe ⁻¹' s) : α) :=
  if_neg hs
#align with_bot.Sup_eq WithBot.sSup_eq

#print WithTop.sInf_empty /-
@[simp]
theorem WithTop.sInf_empty {α : Type _} [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| Set.empty_subset _
#align with_top.cInf_empty WithTop.sInf_empty
-/

#print WithTop.iInf_empty /-
@[simp]
theorem WithTop.iInf_empty {α : Type _} [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    (⨅ i, f i) = ⊤ := by rw [iInf, range_eq_empty, WithTop.sInf_empty]
#align with_top.cinfi_empty WithTop.iInf_empty
-/

#print WithTop.coe_sInf' /-
theorem WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(sInf s) = (sInf (coe '' s) : WithTop α) :=
  by
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs
  · cases h (mem_image_of_mem _ hx)
  · rw [preimage_image_eq]
    exact Option.some_injective _
#align with_top.coe_Inf' WithTop.coe_sInf'
-/

#print WithTop.coe_iInf /-
@[norm_cast]
theorem WithTop.coe_iInf [Nonempty ι] [InfSet α] (f : ι → α) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [iInf, iInf, WithTop.coe_sInf' (range_nonempty f), range_comp]
#align with_top.coe_infi WithTop.coe_iInf
-/

#print WithTop.coe_sSup' /-
theorem WithTop.coe_sSup' [Preorder α] [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup (coe '' s) : WithTop α) :=
  by
  change _ = ite _ _ _
  rw [if_neg, preimage_image_eq, if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, h, ⟨⟩⟩
#align with_top.coe_Sup' WithTop.coe_sSup'
-/

/- warning: with_top.coe_supr -> WithTop.coe_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : SupSet.{u1} α] (f : ι -> α), (BddAbove.{u1} α _inst_1 (Set.range.{u1, u2} α ι f)) -> (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (iSup.{u1, u2} α _inst_2 ι (fun (i : ι) => f i))) (iSup.{u1, u2} (WithTop.{u1} α) (WithTop.hasSup.{u1} α _inst_1 _inst_2) ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : SupSet.{u2} α] (f : ι -> α), (BddAbove.{u2} α _inst_1 (Set.range.{u2, u1} α ι f)) -> (Eq.{succ u2} (WithTop.{u2} α) (WithTop.some.{u2} α (iSup.{u2, u1} α _inst_2 ι (fun (i : ι) => f i))) (iSup.{u2, u1} (WithTop.{u2} α) (instSupSetWithTop.{u2} α _inst_1 _inst_2) ι (fun (i : ι) => WithTop.some.{u2} α (f i))))
Case conversion may be inaccurate. Consider using '#align with_top.coe_supr WithTop.coe_iSupₓ'. -/
@[norm_cast]
theorem WithTop.coe_iSup [Preorder α] [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by rw [iSup, iSup, WithTop.coe_sSup' h, range_comp]
#align with_top.coe_supr WithTop.coe_iSup

/- warning: with_bot.cSup_empty -> WithBot.csSup_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (WithBot.{u1} α) (SupSet.sSup.{u1} (WithBot.{u1} α) (WithBot.hasSup.{u1} α _inst_1) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (WithBot.{u1} α)) (Set.hasEmptyc.{u1} (WithBot.{u1} α)))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (WithBot.{u1} α) (SupSet.sSup.{u1} (WithBot.{u1} α) (instSupSetWithBot.{u1} α _inst_1) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (WithBot.{u1} α)) (Set.instEmptyCollectionSet.{u1} (WithBot.{u1} α)))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))
Case conversion may be inaccurate. Consider using '#align with_bot.cSup_empty WithBot.csSup_emptyₓ'. -/
@[simp]
theorem WithBot.csSup_empty {α : Type _} [SupSet α] : sSup (∅ : Set (WithBot α)) = ⊥ :=
  if_pos <| Set.empty_subset _
#align with_bot.cSup_empty WithBot.csSup_empty

/- warning: with_bot.csupr_empty -> WithBot.ciSup_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : IsEmpty.{u1} ι] [_inst_2 : SupSet.{u2} α] (f : ι -> (WithBot.{u2} α)), Eq.{succ u2} (WithBot.{u2} α) (iSup.{u2, u1} (WithBot.{u2} α) (WithBot.hasSup.{u2} α _inst_2) ι (fun (i : ι) => f i)) (Bot.bot.{u2} (WithBot.{u2} α) (WithBot.hasBot.{u2} α))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : IsEmpty.{u1} ι] [_inst_2 : SupSet.{u2} α] (f : ι -> (WithBot.{u2} α)), Eq.{succ u2} (WithBot.{u2} α) (iSup.{u2, u1} (WithBot.{u2} α) (instSupSetWithBot.{u2} α _inst_2) ι (fun (i : ι) => f i)) (Bot.bot.{u2} (WithBot.{u2} α) (WithBot.bot.{u2} α))
Case conversion may be inaccurate. Consider using '#align with_bot.csupr_empty WithBot.ciSup_emptyₓ'. -/
@[simp]
theorem WithBot.ciSup_empty {α : Type _} [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    (⨆ i, f i) = ⊥ :=
  @WithTop.iInf_empty _ αᵒᵈ _ _ _
#align with_bot.csupr_empty WithBot.ciSup_empty

/- warning: with_bot.coe_Sup' -> WithBot.coe_sSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (SupSet.sSup.{u1} α _inst_1 s)) (SupSet.sSup.{u1} (WithBot.{u1} α) (WithBot.hasSup.{u1} α _inst_1) (Set.image.{u1, u1} α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (SupSet.sSup.{u1} α _inst_1 s)) (SupSet.sSup.{u1} (WithBot.{u1} α) (instSupSetWithBot.{u1} α _inst_1) (Set.image.{u1, u1} α (WithBot.{u1} α) (fun (a : α) => WithBot.some.{u1} α a) s)))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_Sup' WithBot.coe_sSup'ₓ'. -/
@[norm_cast]
theorem WithBot.coe_sSup' [SupSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(sSup s) = (sSup (coe '' s) : WithBot α) :=
  @WithTop.coe_sInf' αᵒᵈ _ _ hs
#align with_bot.coe_Sup' WithBot.coe_sSup'

/- warning: with_bot.coe_supr -> WithBot.coe_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : SupSet.{u1} α] (f : ι -> α), Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (iSup.{u1, u2} α _inst_2 ι (fun (i : ι) => f i))) (iSup.{u1, u2} (WithBot.{u1} α) (WithBot.hasSup.{u1} α _inst_2) ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : SupSet.{u1} α] (f : ι -> α), Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (iSup.{u1, u2} α _inst_2 ι (fun (i : ι) => f i))) (iSup.{u1, u2} (WithBot.{u1} α) (instSupSetWithBot.{u1} α _inst_2) ι (fun (i : ι) => WithBot.some.{u1} α (f i)))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_supr WithBot.coe_iSupₓ'. -/
@[norm_cast]
theorem WithBot.coe_iSup [Nonempty ι] [SupSet α] (f : ι → α) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  @WithTop.coe_iInf αᵒᵈ _ _ _ _
#align with_bot.coe_supr WithBot.coe_iSup

/- warning: with_bot.coe_Inf' -> WithBot.coe_sInf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : InfSet.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α _inst_1 s) -> (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (InfSet.sInf.{u1} α _inst_2 s)) (InfSet.sInf.{u1} (WithBot.{u1} α) (WithBot.hasInf.{u1} α _inst_1 _inst_2) (Set.image.{u1, u1} α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : InfSet.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α _inst_1 s) -> (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (InfSet.sInf.{u1} α _inst_2 s)) (InfSet.sInf.{u1} (WithBot.{u1} α) (instInfSetWithBot.{u1} α _inst_1 _inst_2) (Set.image.{u1, u1} α (WithBot.{u1} α) (fun (a : α) => WithBot.some.{u1} α a) s)))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_Inf' WithBot.coe_sInf'ₓ'. -/
@[norm_cast]
theorem WithBot.coe_sInf' [Preorder α] [InfSet α] {s : Set α} (hs : BddBelow s) :
    ↑(sInf s) = (sInf (coe '' s) : WithBot α) :=
  @WithTop.coe_sSup' αᵒᵈ _ _ _ hs
#align with_bot.coe_Inf' WithBot.coe_sInf'

/- warning: with_bot.coe_infi -> WithBot.coe_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : InfSet.{u1} α] (f : ι -> α), (BddBelow.{u1} α _inst_1 (Set.range.{u1, u2} α ι f)) -> (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (iInf.{u1, u2} α _inst_2 ι (fun (i : ι) => f i))) (iInf.{u1, u2} (WithBot.{u1} α) (WithBot.hasInf.{u1} α _inst_1 _inst_2) ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : InfSet.{u2} α] (f : ι -> α), (BddBelow.{u2} α _inst_1 (Set.range.{u2, u1} α ι f)) -> (Eq.{succ u2} (WithBot.{u2} α) (WithBot.some.{u2} α (iInf.{u2, u1} α _inst_2 ι (fun (i : ι) => f i))) (iInf.{u2, u1} (WithBot.{u2} α) (instInfSetWithBot.{u2} α _inst_1 _inst_2) ι (fun (i : ι) => WithBot.some.{u2} α (f i))))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_infi WithBot.coe_iInfₓ'. -/
@[norm_cast]
theorem WithBot.coe_iInf [Preorder α] [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  @WithTop.coe_iSup αᵒᵈ _ _ _ _ h
#align with_bot.coe_infi WithBot.coe_iInf

end

#print ConditionallyCompleteLattice /-
-- section
/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLattice (α : Type _) extends Lattice α, SupSet α, InfSet α where
  le_cSup : ∀ s a, BddAbove s → a ∈ s → a ≤ Sup s
  cSup_le : ∀ s a, Set.Nonempty s → a ∈ upperBounds s → Sup s ≤ a
  cInf_le : ∀ s a, BddBelow s → a ∈ s → Inf s ≤ a
  le_cInf : ∀ s a, Set.Nonempty s → a ∈ lowerBounds s → a ≤ Inf s
#align conditionally_complete_lattice ConditionallyCompleteLattice
-/

#print ConditionallyCompleteLinearOrder /-
/- ./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure -/
/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrder (α : Type _) extends ConditionallyCompleteLattice α,
  "./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure"
#align conditionally_complete_linear_order ConditionallyCompleteLinearOrder
-/

#print ConditionallyCompleteLinearOrderBot /-
/-- A conditionally complete linear order with `bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrderBot (α : Type _) extends ConditionallyCompleteLinearOrder α,
  Bot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  csSup_empty : Sup ∅ = ⊥
#align conditionally_complete_linear_order_bot ConditionallyCompleteLinearOrderBot
-/

/- warning: conditionally_complete_linear_order_bot.to_order_bot -> ConditionallyCompleteLinearOrderBot.toOrderBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [h : ConditionallyCompleteLinearOrderBot.{u1} α], OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α h)))))))
but is expected to have type
  forall {α : Type.{u1}} [h : ConditionallyCompleteLinearOrderBot.{u1} α], OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α h)))))))
Case conversion may be inaccurate. Consider using '#align conditionally_complete_linear_order_bot.to_order_bot ConditionallyCompleteLinearOrderBot.toOrderBotₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) ConditionallyCompleteLinearOrderBot.toOrderBot
    [h : ConditionallyCompleteLinearOrderBot α] : OrderBot α :=
  { h with }
#align conditionally_complete_linear_order_bot.to_order_bot ConditionallyCompleteLinearOrderBot.toOrderBot

#print CompleteLattice.toConditionallyCompleteLattice /-
-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α :=
  {
    ‹CompleteLattice
        α› with
    le_cSup := by intros <;> apply le_sSup <;> assumption
    cSup_le := by intros <;> apply sSup_le <;> assumption
    cInf_le := by intros <;> apply sInf_le <;> assumption
    le_cInf := by intros <;> apply le_sInf <;> assumption }
#align complete_lattice.to_conditionally_complete_lattice CompleteLattice.toConditionallyCompleteLattice
-/

#print CompleteLinearOrder.toConditionallyCompleteLinearOrderBot /-
-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type _}
    [CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α :=
  { CompleteLattice.toConditionallyCompleteLattice, ‹CompleteLinearOrder α› with
    csSup_empty := sSup_empty }
#align complete_linear_order.to_conditionally_complete_linear_order_bot CompleteLinearOrder.toConditionallyCompleteLinearOrderBot
-/

section

open Classical

/- warning: is_well_order.conditionally_complete_linear_order_bot -> IsWellOrder.conditionallyCompleteLinearOrderBot is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [i₁ : LinearOrder.{u1} α] [i₂ : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α i₁)))))] [h : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α i₁))))))], ConditionallyCompleteLinearOrderBot.{u1} α
but is expected to have type
  forall (α : Type.{u1}) [i₁ : LinearOrder.{u1} α] [i₂ : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α i₁))))))] [h : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.2073 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.2075 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α i₁)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.2073 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.2075)], ConditionallyCompleteLinearOrderBot.{u1} α
Case conversion may be inaccurate. Consider using '#align is_well_order.conditionally_complete_linear_order_bot IsWellOrder.conditionallyCompleteLinearOrderBotₓ'. -/
/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible]
noncomputable def IsWellOrder.conditionallyCompleteLinearOrderBot (α : Type _) [i₁ : LinearOrder α]
    [i₂ : OrderBot α] [h : IsWellOrder α (· < ·)] : ConditionallyCompleteLinearOrderBot α :=
  { i₁, i₂,
    LinearOrder.toLattice with
    sInf := fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥
    cInf_le := fun s a hs has => by
      have s_ne : s.nonempty := ⟨a, has⟩
      simpa [s_ne] using not_lt.1 (h.wf.not_lt_min s s_ne has)
    le_cInf := fun s a hs has => by
      simp only [hs, dif_pos]
      exact has (h.wf.min_mem s hs)
    sSup := fun s => if hs : (upperBounds s).Nonempty then h.wf.min _ hs else ⊥
    le_cSup := fun s a hs has =>
      by
      have h's : (upperBounds s).Nonempty := hs
      simp only [h's, dif_pos]
      exact h.wf.min_mem _ h's has
    cSup_le := fun s a hs has =>
      by
      have h's : (upperBounds s).Nonempty := ⟨a, has⟩
      simp only [h's, dif_pos]
      simpa using h.wf.not_lt_min _ h's has
    csSup_empty := by simpa using eq_bot_iff.2 (not_lt.1 <| h.wf.not_lt_min _ _ <| mem_univ ⊥) }
#align is_well_order.conditionally_complete_linear_order_bot IsWellOrder.conditionallyCompleteLinearOrderBot

end

section OrderDual

instance (α : Type _) [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice αᵒᵈ :=
  { OrderDual.hasInf α, OrderDual.hasSup α,
    OrderDual.lattice
      α with
    le_cSup := @ConditionallyCompleteLattice.cInf_le α _
    cSup_le := @ConditionallyCompleteLattice.le_cInf α _
    le_cInf := @ConditionallyCompleteLattice.cSup_le α _
    cInf_le := @ConditionallyCompleteLattice.le_cSup α _ }

instance (α : Type _) [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder αᵒᵈ :=
  { OrderDual.conditionallyCompleteLattice α, OrderDual.linearOrder α with }

end OrderDual

#print conditionallyCompleteLatticeOfsSup /-
/-- Create a `conditionally_complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a nonempty set which is bounded above. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`conditionally_complete_lattice` instance as
```
instance : conditionally_complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf
  ..conditionally_complete_lattice_of_Sup my_T _ }
```
-/
def conditionallyCompleteLatticeOfsSup (α : Type _) [H1 : PartialOrder α] [H2 : SupSet α]
    (bdd_above_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bdd_below_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (is_lub_Sup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (sSup s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with
    sup := fun a b => sSup {a, b}
    le_sup_left := fun a b =>
      (isLUB_sSup {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    le_sup_right := fun a b =>
      (isLUB_sSup {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    sup_le := fun a b c hac hbc =>
      (isLUB_sSup {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    inf := fun a b => sSup (lowerBounds {a, b})
    inf_le_left := fun a b =>
      (isLUB_sSup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bdd_below_pair a b)).2
        fun c hc => hc <| mem_insert _ _
    inf_le_right := fun a b =>
      (isLUB_sSup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bdd_below_pair a b)).2
        fun c hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    le_inf := fun c a b hca hcb =>
      (isLUB_sSup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hcb) hca⟩).1
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    sInf := fun s => sSup (lowerBounds s)
    cSup_le := fun s a hs ha => (isLUB_sSup s ⟨a, ha⟩ hs).2 ha
    le_cSup := fun s a hs ha => (isLUB_sSup s hs ⟨a, ha⟩).1 ha
    cInf_le := fun s a hs ha =>
      (isLUB_sSup (lowerBounds s) (Nonempty.bddAbove_lowerBounds ⟨a, ha⟩) hs).2 fun b hb => hb ha
    le_cInf := fun s a hs ha => (isLUB_sSup (lowerBounds s) hs.bddAbove_lowerBounds ⟨a, ha⟩).1 ha }
#align conditionally_complete_lattice_of_Sup conditionallyCompleteLatticeOfsSup
-/

#print conditionallyCompleteLatticeOfsInf /-
/-- Create a `conditionally_complete_lattice_of_Inf` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a nonempty set which is bounded below. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`conditionally_complete_lattice` instance as
```
instance : conditionally_complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup
  ..conditionally_complete_lattice_of_Inf my_T _ }
```
-/
def conditionallyCompleteLatticeOfsInf (α : Type _) [H1 : PartialOrder α] [H2 : InfSet α]
    (bdd_above_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bdd_below_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (is_glb_Inf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (sInf s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with
    inf := fun a b => sInf {a, b}
    inf_le_left := fun a b =>
      (isGLB_sInf {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    inf_le_right := fun a b =>
      (isGLB_sInf {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    le_inf := fun c a b hca hcb =>
      (isGLB_sInf {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    sup := fun a b => sInf (upperBounds {a, b})
    le_sup_left := fun a b =>
      (isGLB_sInf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bdd_above_pair a b)).2
        fun c hc => hc <| mem_insert _ _
    le_sup_right := fun a b =>
      (isGLB_sInf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bdd_above_pair a b)).2
        fun c hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    sup_le := fun a b c hac hbc =>
      (isGLB_sInf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hbc) hac⟩).1
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    sSup := fun s => sInf (upperBounds s)
    le_cInf := fun s a hs ha => (isGLB_sInf s ⟨a, ha⟩ hs).2 ha
    cInf_le := fun s a hs ha => (isGLB_sInf s hs ⟨a, ha⟩).1 ha
    le_cSup := fun s a hs ha =>
      (isGLB_sInf (upperBounds s) (Nonempty.bddBelow_upperBounds ⟨a, ha⟩) hs).2 fun b hb => hb ha
    cSup_le := fun s a hs ha => (isGLB_sInf (upperBounds s) hs.bddBelow_upperBounds ⟨a, ha⟩).1 ha }
#align conditionally_complete_lattice_of_Inf conditionallyCompleteLatticeOfsInf
-/

#print conditionallyCompleteLatticeOfLatticeOfsSup /-
/-- A version of `conditionally_complete_lattice_of_Sup` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `Inf` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfsSup (α : Type _) [H1 : Lattice α] [H2 : SupSet α]
    (is_lub_Sup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (sSup s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfsSup α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isLUB_sSup with }
#align conditionally_complete_lattice_of_lattice_of_Sup conditionallyCompleteLatticeOfLatticeOfsSup
-/

#print conditionallyCompleteLatticeOfLatticeOfsInf /-
/-- A version of `conditionally_complete_lattice_of_Inf` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `Sup` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfsInf (α : Type _) [H1 : Lattice α] [H2 : InfSet α]
    (is_glb_Inf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (sInf s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfsInf α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isGLB_sInf with }
#align conditionally_complete_lattice_of_lattice_of_Inf conditionallyCompleteLatticeOfLatticeOfsInf
-/

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

/- warning: le_cSup -> le_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_cSup le_csSupₓ'. -/
theorem le_csSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s :=
  ConditionallyCompleteLattice.le_cSup s a h₁ h₂
#align le_cSup le_csSup

/- warning: cSup_le -> csSup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align cSup_le csSup_leₓ'. -/
theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  ConditionallyCompleteLattice.cSup_le s a h₁ h₂
#align cSup_le csSup_le

/- warning: cInf_le -> csInf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align cInf_le csInf_leₓ'. -/
theorem csInf_le (h₁ : BddBelow s) (h₂ : a ∈ s) : sInf s ≤ a :=
  ConditionallyCompleteLattice.cInf_le s a h₁ h₂
#align cInf_le csInf_le

/- warning: le_cInf -> le_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_cInf le_csInfₓ'. -/
theorem le_csInf (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ sInf s :=
  ConditionallyCompleteLattice.le_cInf s a h₁ h₂
#align le_cInf le_csInf

/- warning: le_cSup_of_le -> le_csSup_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_cSup_of_le le_csSup_of_leₓ'. -/
theorem le_csSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_csSup hs hb)
#align le_cSup_of_le le_csSup_of_le

/- warning: cInf_le_of_le -> csInf_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align cInf_le_of_le csInf_le_of_leₓ'. -/
theorem csInf_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (csInf_le hs hb) h
#align cInf_le_of_le csInf_le_of_le

/- warning: cSup_le_cSup -> csSup_le_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align cSup_le_cSup csSup_le_csSupₓ'. -/
theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
  csSup_le hs fun a ha => le_csSup ht (h ha)
#align cSup_le_cSup csSup_le_csSup

/- warning: cInf_le_cInf -> csInf_le_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) t) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) t) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align cInf_le_cInf csInf_le_csInfₓ'. -/
theorem csInf_le_csInf (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : sInf t ≤ sInf s :=
  le_csInf hs fun a ha => csInf_le ht (h ha)
#align cInf_le_cInf csInf_le_csInf

/- warning: le_cSup_iff -> le_csSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_cSup_iff le_csSup_iffₓ'. -/
theorem le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h b hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun x => le_csSup h⟩
#align le_cSup_iff le_csSup_iff

/- warning: cInf_le_iff -> csInf_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)))
Case conversion may be inaccurate. Consider using '#align cInf_le_iff csInf_le_iffₓ'. -/
theorem csInf_le_iff (h : BddBelow s) (hs : s.Nonempty) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h b hb => le_trans (le_csInf hs hb) h, fun hb => hb _ fun x => csInf_le h⟩
#align cInf_le_iff csInf_le_iff

/- warning: is_lub_cSup -> isLUB_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align is_lub_cSup isLUB_csSupₓ'. -/
theorem isLUB_csSup (ne : s.Nonempty) (H : BddAbove s) : IsLUB s (sSup s) :=
  ⟨fun x => le_csSup H, fun x => csSup_le Ne⟩
#align is_lub_cSup isLUB_csSup

/- warning: is_lub_csupr -> isLUB_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align is_lub_csupr isLUB_ciSupₓ'. -/
theorem isLUB_ciSup [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csSup (range_nonempty f) H
#align is_lub_csupr isLUB_ciSup

/- warning: is_lub_csupr_set -> isLUB_ciSup_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (Set.Nonempty.{u2} β s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (Set.Nonempty.{u2} β s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))))
Case conversion may be inaccurate. Consider using '#align is_lub_csupr_set isLUB_ciSup_setₓ'. -/
theorem isLUB_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact isLUB_csSup (Hne.image _) H
#align is_lub_csupr_set isLUB_ciSup_set

/- warning: is_glb_cInf -> isGLB_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align is_glb_cInf isGLB_csInfₓ'. -/
theorem isGLB_csInf (ne : s.Nonempty) (H : BddBelow s) : IsGLB s (sInf s) :=
  ⟨fun x => csInf_le H, fun x => le_csInf Ne⟩
#align is_glb_cInf isGLB_csInf

/- warning: is_glb_cinfi -> isGLB_ciInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align is_glb_cinfi isGLB_ciInfₓ'. -/
theorem isGLB_ciInf [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_csInf (range_nonempty f) H
#align is_glb_cinfi isGLB_ciInf

/- warning: is_glb_cinfi_set -> isGLB_ciInf_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (Set.Nonempty.{u2} β s) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (Set.Nonempty.{u2} β s) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))))
Case conversion may be inaccurate. Consider using '#align is_glb_cinfi_set isGLB_ciInf_setₓ'. -/
theorem isGLB_ciInf_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  @isLUB_ciSup_set αᵒᵈ _ _ _ _ H Hne
#align is_glb_cinfi_set isGLB_ciInf_set

/- warning: csupr_le_iff -> ciSup_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f) a) (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι f) a) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align csupr_le_iff ciSup_le_iffₓ'. -/
theorem ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_range_iff
#align csupr_le_iff ciSup_le_iff

/- warning: le_cinfi_iff -> le_ciInf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f i)))
Case conversion may be inaccurate. Consider using '#align le_cinfi_iff le_ciInf_iffₓ'. -/
theorem le_ciInf_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf hf).trans forall_range_iff
#align le_cinfi_iff le_ciInf_iff

/- warning: csupr_set_le_iff -> ciSup_set_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> α} {a : α}, (Set.Nonempty.{u2} ι s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} ι α f s)) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i))) a) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> α} {a : α}, (Set.Nonempty.{u2} ι s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} ι α f s)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i))) a) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) a)))
Case conversion may be inaccurate. Consider using '#align csupr_set_le_iff ciSup_set_le_iffₓ'. -/
theorem ciSup_set_le_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : (⨆ i : s, f i) ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans ball_image_iff
#align csupr_set_le_iff ciSup_set_le_iff

/- warning: le_cinfi_set_iff -> le_ciInf_set_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> α} {a : α}, (Set.Nonempty.{u2} ι s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} ι α f s)) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i)))) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> α} {a : α}, (Set.Nonempty.{u2} ι s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} ι α f s)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i)))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f i))))
Case conversion may be inaccurate. Consider using '#align le_cinfi_set_iff le_ciInf_set_iffₓ'. -/
theorem le_ciInf_set_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans ball_image_iff
#align le_cinfi_set_iff le_ciInf_set_iff

/- warning: is_lub.cSup_eq -> IsLUB.csSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_lub.cSup_eq IsLUB.csSup_eqₓ'. -/
theorem IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a :=
  (isLUB_csSup Ne ⟨a, H.1⟩).unique H
#align is_lub.cSup_eq IsLUB.csSup_eq

/- warning: is_lub.csupr_eq -> IsLUB.ciSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i)) a)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => f i)) a)
Case conversion may be inaccurate. Consider using '#align is_lub.csupr_eq IsLUB.ciSup_eqₓ'. -/
theorem IsLUB.ciSup_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : (⨆ i, f i) = a :=
  H.csSup_eq (range_nonempty f)
#align is_lub.csupr_eq IsLUB.ciSup_eq

/- warning: is_lub.csupr_set_eq -> IsLUB.ciSup_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {s : Set.{u2} β} {f : β -> α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) a) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} α (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {s : Set.{u2} β} {f : β -> α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) a) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} α (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))) a)
Case conversion may be inaccurate. Consider using '#align is_lub.csupr_set_eq IsLUB.ciSup_set_eqₓ'. -/
theorem IsLUB.ciSup_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    (⨆ i : s, f i) = a :=
  IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_lub.csupr_set_eq IsLUB.ciSup_set_eq

/- warning: is_greatest.cSup_eq -> IsGreatest.csSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGreatest.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGreatest.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_greatest.cSup_eq IsGreatest.csSup_eqₓ'. -/
/-- A greatest element of a set is the supremum of this set. -/
theorem IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s = a :=
  H.IsLUB.csSup_eq H.Nonempty
#align is_greatest.cSup_eq IsGreatest.csSup_eq

/- warning: is_greatest.Sup_mem -> IsGreatest.csSup_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGreatest.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGreatest.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) s)
Case conversion may be inaccurate. Consider using '#align is_greatest.Sup_mem IsGreatest.csSup_memₓ'. -/
theorem IsGreatest.csSup_mem (H : IsGreatest s a) : sSup s ∈ s :=
  H.csSup_eq.symm ▸ H.1
#align is_greatest.Sup_mem IsGreatest.csSup_mem

/- warning: is_glb.cInf_eq -> IsGLB.csInf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_glb.cInf_eq IsGLB.csInf_eqₓ'. -/
theorem IsGLB.csInf_eq (H : IsGLB s a) (ne : s.Nonempty) : sInf s = a :=
  (isGLB_csInf Ne ⟨a, H.1⟩).unique H
#align is_glb.cInf_eq IsGLB.csInf_eq

/- warning: is_glb.cinfi_eq -> IsGLB.ciInf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => f i)) a)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => f i)) a)
Case conversion may be inaccurate. Consider using '#align is_glb.cinfi_eq IsGLB.ciInf_eqₓ'. -/
theorem IsGLB.ciInf_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : (⨅ i, f i) = a :=
  H.csInf_eq (range_nonempty f)
#align is_glb.cinfi_eq IsGLB.ciInf_eq

/- warning: is_glb.cinfi_set_eq -> IsGLB.ciInf_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {s : Set.{u2} β} {f : β -> α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) a) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} α (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {s : Set.{u2} β} {f : β -> α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) a) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} α (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))) a)
Case conversion may be inaccurate. Consider using '#align is_glb.cinfi_set_eq IsGLB.ciInf_set_eqₓ'. -/
theorem IsGLB.ciInf_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    (⨅ i : s, f i) = a :=
  IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_glb.cinfi_set_eq IsGLB.ciInf_set_eq

/- warning: is_least.cInf_eq -> IsLeast.csInf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_least.cInf_eq IsLeast.csInf_eqₓ'. -/
/-- A least element of a set is the infimum of this set. -/
theorem IsLeast.csInf_eq (H : IsLeast s a) : sInf s = a :=
  H.IsGLB.csInf_eq H.Nonempty
#align is_least.cInf_eq IsLeast.csInf_eq

/- warning: is_least.Inf_mem -> IsLeast.csInf_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) s)
Case conversion may be inaccurate. Consider using '#align is_least.Inf_mem IsLeast.csInf_memₓ'. -/
theorem IsLeast.csInf_mem (H : IsLeast s a) : sInf s ∈ s :=
  H.csInf_eq.symm ▸ H.1
#align is_least.Inf_mem IsLeast.csInf_mem

/- warning: subset_Icc_cInf_cSup -> subset_Icc_csInf_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align subset_Icc_cInf_cSup subset_Icc_csInf_csSupₓ'. -/
theorem subset_Icc_csInf_csSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (sInf s) (sSup s) :=
  fun x hx => ⟨csInf_le hb hx, le_csSup ha hx⟩
#align subset_Icc_cInf_cSup subset_Icc_csInf_csSup

/- warning: cSup_le_iff -> csSup_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)))
Case conversion may be inaccurate. Consider using '#align cSup_le_iff csSup_le_iffₓ'. -/
theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csSup hs hb)
#align cSup_le_iff csSup_le_iff

/- warning: le_cInf_iff -> le_csInf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_cInf_iff le_csInf_iffₓ'. -/
theorem le_csInf_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_csInf hs hb)
#align le_cInf_iff le_csInf_iff

/- warning: cSup_lower_bounds_eq_cInf -> csSup_lower_bounds_eq_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align cSup_lower_bounds_eq_cInf csSup_lower_bounds_eq_csInfₓ'. -/
theorem csSup_lower_bounds_eq_csInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    sSup (lowerBounds s) = sInf s :=
  (isLUB_csSup h <| hs.mono fun x hx y hy => hy hx).unique (isGLB_csInf hs h).IsLUB
#align cSup_lower_bounds_eq_cInf csSup_lower_bounds_eq_csInf

/- warning: cInf_upper_bounds_eq_cSup -> csInf_upper_bounds_eq_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align cInf_upper_bounds_eq_cSup csInf_upper_bounds_eq_csSupₓ'. -/
theorem csInf_upper_bounds_eq_csSup {s : Set α} (h : BddAbove s) (hs : s.Nonempty) :
    sInf (upperBounds s) = sSup s :=
  (isGLB_csInf h <| hs.mono fun x hx y hy => hy hx).unique (isLUB_csSup hs h).IsGLB
#align cInf_upper_bounds_eq_cSup csInf_upper_bounds_eq_csSup

/- warning: not_mem_of_lt_cInf -> not_mem_of_lt_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {x : α} {s : Set.{u1} α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) x (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {x : α} {s : Set.{u1} α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) x (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s)) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))
Case conversion may be inaccurate. Consider using '#align not_mem_of_lt_cInf not_mem_of_lt_csInfₓ'. -/
theorem not_mem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))
#align not_mem_of_lt_cInf not_mem_of_lt_csInf

/- warning: not_mem_of_cSup_lt -> not_mem_of_csSup_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {x : α} {s : Set.{u1} α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) x) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {x : α} {s : Set.{u1} α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) x) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))
Case conversion may be inaccurate. Consider using '#align not_mem_of_cSup_lt not_mem_of_csSup_ltₓ'. -/
theorem not_mem_of_csSup_lt {x : α} {s : Set α} (h : sSup s < x) (hs : BddAbove s) : x ∉ s :=
  @not_mem_of_lt_csInf αᵒᵈ _ x s h hs
#align not_mem_of_cSup_lt not_mem_of_csSup_lt

/- warning: cSup_eq_of_forall_le_of_forall_lt_exists_gt -> csSup_eq_of_forall_le_of_forall_lt_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w b) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w a)))) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w b) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w a)))) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align cSup_eq_of_forall_le_of_forall_lt_exists_gt csSup_eq_of_forall_le_of_forall_lt_exists_gtₓ'. -/
/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `Sup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  eq_of_le_of_not_lt (csSup_le hs H) fun hb =>
    let ⟨a, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_csSup ⟨b, H⟩ ha
#align cSup_eq_of_forall_le_of_forall_lt_exists_gt csSup_eq_of_forall_le_of_forall_lt_exists_gt

/- warning: cInf_eq_of_forall_ge_of_forall_gt_exists_lt -> csInf_eq_of_forall_ge_of_forall_gt_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b w) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a w)))) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b w) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a w)))) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align cInf_eq_of_forall_ge_of_forall_gt_exists_lt csInf_eq_of_forall_ge_of_forall_gt_exists_ltₓ'. -/
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `Inf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem csInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → sInf s = b :=
  @csSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align cInf_eq_of_forall_ge_of_forall_gt_exists_lt csInf_eq_of_forall_ge_of_forall_gt_exists_lt

/- warning: lt_cSup_of_lt -> lt_csSup_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align lt_cSup_of_lt lt_csSup_of_ltₓ'. -/
/-- b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem lt_csSup_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_csSup hs ha)
#align lt_cSup_of_lt lt_csSup_of_lt

/- warning: cInf_lt_of_lt -> csInf_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align cInf_lt_of_lt csInf_lt_of_ltₓ'. -/
/-- Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem csInf_lt_of_lt : BddBelow s → a ∈ s → a < b → sInf s < b :=
  @lt_csSup_of_lt αᵒᵈ _ _ _ _
#align cInf_lt_of_lt csInf_lt_of_lt

/- warning: exists_between_of_forall_le -> exists_between_of_forall_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α t) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) x y))) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α t) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) x y))) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t)))
Case conversion may be inaccurate. Consider using '#align exists_between_of_forall_le exists_between_of_forall_leₓ'. -/
/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨sInf t, fun x hx => le_csInf tne <| hst x hx, fun y hy => csInf_le (sne.mono hst) hy⟩
#align exists_between_of_forall_le exists_between_of_forall_le

/- warning: cSup_singleton -> csSup_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) a
Case conversion may be inaccurate. Consider using '#align cSup_singleton csSup_singletonₓ'. -/
/-- The supremum of a singleton is the element of the singleton-/
@[simp]
theorem csSup_singleton (a : α) : sSup {a} = a :=
  isGreatest_singleton.csSup_eq
#align cSup_singleton csSup_singleton

/- warning: cInf_singleton -> csInf_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) a
Case conversion may be inaccurate. Consider using '#align cInf_singleton csInf_singletonₓ'. -/
/-- The infimum of a singleton is the element of the singleton-/
@[simp]
theorem csInf_singleton (a : α) : sInf {a} = a :=
  isLeast_singleton.csInf_eq
#align cInf_singleton csInf_singleton

/- warning: cSup_pair -> csSup_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align cSup_pair csSup_pairₓ'. -/
@[simp]
theorem csSup_pair (a b : α) : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)
#align cSup_pair csSup_pair

/- warning: cInf_pair -> csInf_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α) (b : α), Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α) (b : α), Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align cInf_pair csInf_pairₓ'. -/
@[simp]
theorem csInf_pair (a b : α) : sInf {a, b} = a ⊓ b :=
  (@isGLB_pair _ _ a b).csInf_eq (insert_nonempty _ _)
#align cInf_pair csInf_pair

/- warning: cInf_le_cSup -> csInf_le_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align cInf_le_cSup csInf_le_csSupₓ'. -/
/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem csInf_le_csSup (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_csInf Ne hb) (isLUB_csSup Ne ha) Ne
#align cInf_le_cSup csInf_le_csSup

/- warning: cSup_union -> csSup_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) t)))
Case conversion may be inaccurate. Consider using '#align cSup_union csSup_unionₓ'. -/
/-- The sup of a union of two sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem csSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl
#align cSup_union csSup_union

/- warning: cInf_union -> csInf_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) t)))
Case conversion may be inaccurate. Consider using '#align cInf_union csInf_unionₓ'. -/
/-- The inf of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem csInf_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    sInf (s ∪ t) = sInf s ⊓ sInf t :=
  @csSup_union αᵒᵈ _ _ _ hs sne ht tne
#align cInf_union csInf_union

/- warning: cSup_inter_le -> csSup_inter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) t)))
Case conversion may be inaccurate. Consider using '#align cSup_inter_le csSup_inter_leₓ'. -/
/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem csSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  csSup_le hst fun x hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)
#align cSup_inter_le csSup_inter_le

/- warning: le_cInf_inter -> le_csInf_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) t)) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) t)) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align le_cInf_inter le_csInf_interₓ'. -/
/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_csInf_inter :
    BddBelow s → BddBelow t → (s ∩ t).Nonempty → sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  @csSup_inter_le αᵒᵈ _ _ _
#align le_cInf_inter le_csInf_inter

/- warning: cSup_insert -> csSup_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align cSup_insert csSup_insertₓ'. -/
/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem csSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)
#align cSup_insert csSup_insert

/- warning: cInf_insert -> csInf_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) a (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align cInf_insert csInf_insertₓ'. -/
/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem csInf_insert (hs : BddBelow s) (sne : s.Nonempty) : sInf (insert a s) = a ⊓ sInf s :=
  @csSup_insert αᵒᵈ _ _ _ hs sne
#align cInf_insert csInf_insert

/- warning: cInf_Icc -> csInf_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
Case conversion may be inaccurate. Consider using '#align cInf_Icc csInf_Iccₓ'. -/
@[simp]
theorem csInf_Icc (h : a ≤ b) : sInf (Icc a b) = a :=
  (isGLB_Icc h).csInf_eq (nonempty_Icc.2 h)
#align cInf_Icc csInf_Icc

/- warning: cInf_Ici -> csInf_Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
Case conversion may be inaccurate. Consider using '#align cInf_Ici csInf_Iciₓ'. -/
@[simp]
theorem csInf_Ici : sInf (Ici a) = a :=
  isLeast_Ici.csInf_eq
#align cInf_Ici csInf_Ici

/- warning: cInf_Ico -> csInf_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
Case conversion may be inaccurate. Consider using '#align cInf_Ico csInf_Icoₓ'. -/
@[simp]
theorem csInf_Ico (h : a < b) : sInf (Ico a b) = a :=
  (isGLB_Ico h).csInf_eq (nonempty_Ico.2 h)
#align cInf_Ico csInf_Ico

/- warning: cInf_Ioc -> csInf_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
Case conversion may be inaccurate. Consider using '#align cInf_Ioc csInf_Iocₓ'. -/
@[simp]
theorem csInf_Ioc [DenselyOrdered α] (h : a < b) : sInf (Ioc a b) = a :=
  (isGLB_Ioc h).csInf_eq (nonempty_Ioc.2 h)
#align cInf_Ioc csInf_Ioc

/- warning: cInf_Ioi -> csInf_Ioi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
Case conversion may be inaccurate. Consider using '#align cInf_Ioi csInf_Ioiₓ'. -/
@[simp]
theorem csInf_Ioi [NoMaxOrder α] [DenselyOrdered α] : sInf (Ioi a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_lt) fun w hw => by
    simpa using exists_between hw
#align cInf_Ioi csInf_Ioi

/- warning: cInf_Ioo -> csInf_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
Case conversion may be inaccurate. Consider using '#align cInf_Ioo csInf_Iooₓ'. -/
@[simp]
theorem csInf_Ioo [DenselyOrdered α] (h : a < b) : sInf (Ioo a b) = a :=
  (isGLB_Ioo h).csInf_eq (nonempty_Ioo.2 h)
#align cInf_Ioo csInf_Ioo

/- warning: cSup_Icc -> csSup_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
Case conversion may be inaccurate. Consider using '#align cSup_Icc csSup_Iccₓ'. -/
@[simp]
theorem csSup_Icc (h : a ≤ b) : sSup (Icc a b) = b :=
  (isLUB_Icc h).csSup_eq (nonempty_Icc.2 h)
#align cSup_Icc csSup_Icc

/- warning: cSup_Ico -> csSup_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
Case conversion may be inaccurate. Consider using '#align cSup_Ico csSup_Icoₓ'. -/
@[simp]
theorem csSup_Ico [DenselyOrdered α] (h : a < b) : sSup (Ico a b) = b :=
  (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)
#align cSup_Ico csSup_Ico

/- warning: cSup_Iic -> csSup_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
Case conversion may be inaccurate. Consider using '#align cSup_Iic csSup_Iicₓ'. -/
@[simp]
theorem csSup_Iic : sSup (Iic a) = a :=
  isGreatest_Iic.csSup_eq
#align cSup_Iic csSup_Iic

/- warning: cSup_Iio -> csSup_Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : NoMinOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
Case conversion may be inaccurate. Consider using '#align cSup_Iio csSup_Iioₓ'. -/
@[simp]
theorem csSup_Iio [NoMinOrder α] [DenselyOrdered α] : sSup (Iio a) = a :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm'] using exists_between hw
#align cSup_Iio csSup_Iio

/- warning: cSup_Ioc -> csSup_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
Case conversion may be inaccurate. Consider using '#align cSup_Ioc csSup_Iocₓ'. -/
@[simp]
theorem csSup_Ioc (h : a < b) : sSup (Ioc a b) = b :=
  (isLUB_Ioc h).csSup_eq (nonempty_Ioc.2 h)
#align cSup_Ioc csSup_Ioc

/- warning: cSup_Ioo -> csSup_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
Case conversion may be inaccurate. Consider using '#align cSup_Ioo csSup_Iooₓ'. -/
@[simp]
theorem csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b :=
  (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)
#align cSup_Ioo csSup_Ioo

/- warning: csupr_le -> ciSup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {c : α}, (forall (x : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f x) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f) c)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {c : α}, (forall (x : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f x) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι f) c)
Case conversion may be inaccurate. Consider using '#align csupr_le ciSup_leₓ'. -/
/-- The indexed supremum of a function is bounded above by a uniform bound-/
theorem ciSup_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : iSup f ≤ c :=
  csSup_le (range_nonempty f) (by rwa [forall_range_iff])
#align csupr_le ciSup_le

/- warning: le_csupr -> le_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (c : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f c) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : ι -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (c : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (f c) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align le_csupr le_ciSupₓ'. -/
/-- The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_ciSup {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ iSup f :=
  le_csSup H (mem_range_self _)
#align le_csupr le_ciSup

/- warning: le_csupr_of_le -> le_ciSup_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (c : ι), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {a : α} {f : ι -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (c : ι), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) a (f c)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) a (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) ι f)))
Case conversion may be inaccurate. Consider using '#align le_csupr_of_le le_ciSup_of_leₓ'. -/
theorem le_ciSup_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  le_trans h (le_ciSup H c)
#align le_csupr_of_le le_ciSup_of_le

/- warning: csupr_mono -> ciSup_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι g)) -> (forall (x : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f x) (g x)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι g)) -> (forall (x : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (f x) (g x)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) ι f) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) ι g))
Case conversion may be inaccurate. Consider using '#align csupr_mono ciSup_monoₓ'. -/
/-- The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem ciSup_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) : iSup f ≤ iSup g :=
  by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)
#align csupr_mono ciSup_mono

/- warning: le_csupr_set -> le_ciSup_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (forall {c : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f c) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (forall {c : β}, (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f c) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i)))))
Case conversion may be inaccurate. Consider using '#align le_csupr_set le_ciSup_setₓ'. -/
theorem le_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'
#align le_csupr_set le_ciSup_set

/- warning: cinfi_mono -> ciInf_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (x : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f x) (g x)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (x : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (f x) (g x)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (iInf.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) ι f) (iInf.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) ι g))
Case conversion may be inaccurate. Consider using '#align cinfi_mono ciInf_monoₓ'. -/
/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem ciInf_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : iInf f ≤ iInf g :=
  @ciSup_mono αᵒᵈ _ _ _ _ B H
#align cinfi_mono ciInf_mono

/- warning: le_cinfi -> le_ciInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {c : α}, (forall (x : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) c (f x)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) c (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {c : α}, (forall (x : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) c (f x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) c (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align le_cinfi le_ciInfₓ'. -/
/-- The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_ciInf [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ iInf f :=
  @ciSup_le αᵒᵈ _ _ _ _ _ H
#align le_cinfi le_ciInf

/- warning: cinfi_le -> ciInf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (c : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f) (f c))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : ι -> α}, (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (c : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (iInf.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) ι f) (f c))
Case conversion may be inaccurate. Consider using '#align cinfi_le ciInf_leₓ'. -/
/-- The indexed infimum of a function is bounded above by the value taken at one point-/
theorem ciInf_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : iInf f ≤ f c :=
  @le_ciSup αᵒᵈ _ _ _ H c
#align cinfi_le ciInf_le

/- warning: cinfi_le_of_le -> ciInf_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (c : ι), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f c) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {a : α} {f : ι -> α}, (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (c : ι), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (f c) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (iInf.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) ι f) a))
Case conversion may be inaccurate. Consider using '#align cinfi_le_of_le ciInf_le_of_leₓ'. -/
theorem ciInf_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : iInf f ≤ a :=
  @le_ciSup_of_le αᵒᵈ _ _ _ _ H c h
#align cinfi_le_of_le ciInf_le_of_le

/- warning: cinfi_set_le -> ciInf_set_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (forall {c : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))) (f c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (forall {c : β}, (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))) (f c)))
Case conversion may be inaccurate. Consider using '#align cinfi_set_le ciInf_set_leₓ'. -/
theorem ciInf_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    (⨅ i : s, f i) ≤ f c :=
  @le_ciSup_set αᵒᵈ _ _ _ _ H _ hc
#align cinfi_set_le ciInf_set_le

/- warning: csupr_const -> ciSup_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [hι : Nonempty.{u2} ι] {a : α}, Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (b : ι) => a)) a
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [hι : Nonempty.{u2} ι] {a : α}, Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (b : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align csupr_const ciSup_constₓ'. -/
@[simp]
theorem ciSup_const [hι : Nonempty ι] {a : α} : (⨆ b : ι, a) = a := by
  rw [iSup, range_const, csSup_singleton]
#align csupr_const ciSup_const

/- warning: cinfi_const -> ciInf_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [hι : Nonempty.{u2} ι] {a : α}, Eq.{succ u1} α (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (b : ι) => a)) a
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [hι : Nonempty.{u2} ι] {a : α}, Eq.{succ u1} α (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (b : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align cinfi_const ciInf_constₓ'. -/
@[simp]
theorem ciInf_const [hι : Nonempty ι] {a : α} : (⨅ b : ι, a) = a :=
  @ciSup_const αᵒᵈ _ _ _ _
#align cinfi_const ciInf_const

/- warning: supr_unique -> ciSup_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Unique.{u2} ι] {s : ι -> α}, Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => s i)) (s (Inhabited.default.{u2} ι (Unique.inhabited.{u2} ι _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Unique.{u2} ι] {s : ι -> α}, Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => s i)) (s (Inhabited.default.{u2} ι (Unique.instInhabited.{u2} ι _inst_2)))
Case conversion may be inaccurate. Consider using '#align supr_unique ciSup_uniqueₓ'. -/
@[simp]
theorem ciSup_unique [Unique ι] {s : ι → α} : (⨆ i, s i) = s default :=
  by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, ciSup_const]
#align supr_unique ciSup_unique

/- warning: infi_unique -> ciInf_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Unique.{u2} ι] {s : ι -> α}, Eq.{succ u1} α (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => s i)) (s (Inhabited.default.{u2} ι (Unique.inhabited.{u2} ι _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Unique.{u2} ι] {s : ι -> α}, Eq.{succ u1} α (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => s i)) (s (Inhabited.default.{u2} ι (Unique.instInhabited.{u2} ι _inst_2)))
Case conversion may be inaccurate. Consider using '#align infi_unique ciInf_uniqueₓ'. -/
@[simp]
theorem ciInf_unique [Unique ι] {s : ι → α} : (⨅ i, s i) = s default :=
  @ciSup_unique αᵒᵈ _ _ _ _
#align infi_unique ciInf_unique

/- warning: csupr_pos -> ciSup_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
Case conversion may be inaccurate. Consider using '#align csupr_pos ciSup_posₓ'. -/
@[simp]
theorem ciSup_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  haveI := uniqueProp hp
  ciSup_unique
#align csupr_pos ciSup_pos

/- warning: cinfi_pos -> ciInf_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
Case conversion may be inaccurate. Consider using '#align cinfi_pos ciInf_posₓ'. -/
@[simp]
theorem ciInf_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  @ciSup_pos αᵒᵈ _ _ _ hp
#align cinfi_pos ciInf_pos

/- warning: csupr_eq_of_forall_le_of_forall_lt_exists_gt -> ciSup_eq_of_forall_le_of_forall_lt_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) b) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w b) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w (f i)))) -> (Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i)) b)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) b) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w b) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w (f i)))) -> (Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => f i)) b)
Case conversion may be inaccurate. Consider using '#align csupr_eq_of_forall_le_of_forall_lt_exists_gt ciSup_eq_of_forall_le_of_forall_lt_exists_gtₓ'. -/
/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `supr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_range_iff.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw
#align csupr_eq_of_forall_le_of_forall_lt_exists_gt ciSup_eq_of_forall_le_of_forall_lt_exists_gt

/- warning: cinfi_eq_of_forall_ge_of_forall_gt_exists_lt -> ciInf_eq_of_forall_ge_of_forall_gt_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b (f i)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b w) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) w))) -> (Eq.{succ u1} α (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => f i)) b)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b (f i)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b w) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) w))) -> (Eq.{succ u1} α (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => f i)) b)
Case conversion may be inaccurate. Consider using '#align cinfi_eq_of_forall_ge_of_forall_gt_exists_lt ciInf_eq_of_forall_ge_of_forall_gt_exists_ltₓ'. -/
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `infi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem ciInf_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : (⨅ i : ι, f i) = b :=
  @ciSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _ ‹_› ‹_› ‹_›
#align cinfi_eq_of_forall_ge_of_forall_gt_exists_lt ciInf_eq_of_forall_ge_of_forall_gt_exists_lt

/- warning: monotone.csupr_mem_Inter_Icc_of_antitone -> Monotone.ciSup_mem_Inter_Icc_of_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : β -> α} {g : β -> α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) f) -> (Antitone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) g) -> (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) f g) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) β (fun (n : β) => f n)) (Set.iInter.{u1, succ u2} α β (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : β -> α} {g : β -> α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) f) -> (Antitone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) g) -> (LE.le.{max u1 u2} (β -> α) (Pi.hasLe.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) f g) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) β (fun (n : β) => f n)) (Set.iInter.{u1, succ u2} α β (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))))
Case conversion may be inaccurate. Consider using '#align monotone.csupr_mem_Inter_Icc_of_antitone Monotone.ciSup_mem_Inter_Icc_of_antitoneₓ'. -/
/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.ciSup_mem_Inter_Icc_of_antitone [SemilatticeSup β] {f g : β → α} (hf : Monotone f)
    (hg : Antitone g) (h : f ≤ g) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  by
  refine' mem_Inter.2 fun n => _
  haveI : Nonempty β := ⟨n⟩
  have : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  exact ⟨le_ciSup ⟨g <| n, forall_range_iff.2 this⟩ _, ciSup_le this⟩
#align monotone.csupr_mem_Inter_Icc_of_antitone Monotone.ciSup_mem_Inter_Icc_of_antitone

/- warning: csupr_mem_Inter_Icc_of_antitone_Icc -> ciSup_mem_Inter_Icc_of_antitone_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : β -> α} {g : β -> α}, (Antitone.{u2, u1} β (Set.{u1} α) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))) -> (forall (n : β), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f n) (g n)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) β (fun (n : β) => f n)) (Set.iInter.{u1, succ u2} α β (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : β -> α} {g : β -> α}, (Antitone.{u2, u1} β (Set.{u1} α) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))) -> (forall (n : β), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f n) (g n)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) β (fun (n : β) => f n)) (Set.iInter.{u1, succ u2} α β (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))))
Case conversion may be inaccurate. Consider using '#align csupr_mem_Inter_Icc_of_antitone_Icc ciSup_mem_Inter_Icc_of_antitone_Iccₓ'. -/
/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem ciSup_mem_Inter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.ciSup_mem_Inter_Icc_of_antitone
    (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'
#align csupr_mem_Inter_Icc_of_antitone_Icc ciSup_mem_Inter_Icc_of_antitone_Icc

/- warning: cSup_eq_of_is_forall_le_of_forall_le_imp_ge -> csSup_eq_of_is_forall_le_of_forall_le_imp_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (forall (ub : α), (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a ub)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b ub)) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (forall (ub : α), (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a ub)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b ub)) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align cSup_eq_of_is_forall_le_of_forall_le_imp_ge csSup_eq_of_is_forall_le_of_forall_le_imp_geₓ'. -/
/-- Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : sSup s = b :=
  (csSup_le hs h_is_ub).antisymm (h_b_le_ub _ fun a => le_csSup ⟨b, h_is_ub⟩)
#align cSup_eq_of_is_forall_le_of_forall_le_imp_ge csSup_eq_of_is_forall_le_of_forall_le_imp_ge

end ConditionallyCompleteLattice

#print Pi.conditionallyCompleteLattice /-
instance Pi.conditionallyCompleteLattice {ι : Type _} {α : ∀ i : ι, Type _}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) :=
  { Pi.lattice, Pi.supSet,
    Pi.infSet with
    le_cSup := fun s f ⟨g, hg⟩ hf i =>
      le_csSup ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    cSup_le := fun s f hs hf i =>
      csSup_le (by haveI := hs.to_subtype <;> apply range_nonempty) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i
    cInf_le := fun s f ⟨g, hg⟩ hf i =>
      csInf_le ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    le_cInf := fun s f hs hf i =>
      le_csInf (by haveI := hs.to_subtype <;> apply range_nonempty) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i }
#align pi.conditionally_complete_lattice Pi.conditionallyCompleteLattice
-/

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/- warning: exists_lt_of_lt_cSup -> exists_lt_of_lt_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b a)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_lt_cSup exists_lt_of_lt_csSupₓ'. -/
/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
theorem exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b < sSup s) : ∃ a ∈ s, b < a :=
  by
  contrapose! hb
  exact csSup_le hs hb
#align exists_lt_of_lt_cSup exists_lt_of_lt_csSup

/- warning: exists_lt_of_lt_csupr -> exists_lt_of_lt_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f)) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f)) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (f i)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_lt_csupr exists_lt_of_lt_ciSupₓ'. -/
/-- Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_ciSup [Nonempty ι] {f : ι → α} (h : b < iSup f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩
#align exists_lt_of_lt_csupr exists_lt_of_lt_ciSup

/- warning: exists_lt_of_cInf_lt -> exists_lt_of_csInf_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) b) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) b) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) a b)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_cInf_lt exists_lt_of_csInf_ltₓ'. -/
/-- When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
theorem exists_lt_of_csInf_lt (hs : s.Nonempty) (hb : sInf s < b) : ∃ a ∈ s, a < b :=
  @exists_lt_of_lt_csSup αᵒᵈ _ _ _ hs hb
#align exists_lt_of_cInf_lt exists_lt_of_csInf_lt

/- warning: exists_lt_of_cinfi_lt -> exists_lt_of_ciInf_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f) a) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f) a) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_cinfi_lt exists_lt_of_ciInf_ltₓ'. -/
/-- Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_ciInf_lt [Nonempty ι] {f : ι → α} (h : iInf f < a) : ∃ i, f i < a :=
  @exists_lt_of_lt_ciSup αᵒᵈ _ _ _ _ _ h
#align exists_lt_of_cinfi_lt exists_lt_of_ciInf_lt

open Function

variable [IsWellOrder α (· < ·)]

/- warning: Inf_eq_argmin_on -> sInf_eq_argmin_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))] (hs : Set.Nonempty.{u1} α s), Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) (Function.argminOn.{u1, u1} α α (id.{succ u1} α) (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (IsWellFounded.wf.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))))) (IsWellOrder.to_isWellFounded.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))))) _inst_2)) s hs)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9222 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9224 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9222 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9224)] (hs : Set.Nonempty.{u1} α s), Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) (Function.argminOn.{u1, u1} α α (id.{succ u1} α) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (IsWellFounded.wf.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9249 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9251 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9249 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9251) (IsWellOrder.toIsWellFounded.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9249 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9251 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9249 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9251) _inst_2)) s hs)
Case conversion may be inaccurate. Consider using '#align Inf_eq_argmin_on sInf_eq_argmin_onₓ'. -/
theorem sInf_eq_argmin_on (hs : s.Nonempty) :
    sInf s = argminOn id (@IsWellFounded.wf α (· < ·) _) s hs :=
  IsLeast.csInf_eq ⟨argminOn_mem _ _ _ _, fun a ha => argminOn_le id _ _ ha⟩
#align Inf_eq_argmin_on sInf_eq_argmin_on

/- warning: is_least_Inf -> isLeast_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))], (Set.Nonempty.{u1} α s) -> (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9302 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9304 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9302 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9304)], (Set.Nonempty.{u1} α s) -> (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align is_least_Inf isLeast_csInfₓ'. -/
theorem isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s) :=
  by
  rw [sInf_eq_argmin_on hs]
  exact ⟨argmin_on_mem _ _ _ _, fun a ha => argmin_on_le id _ _ ha⟩
#align is_least_Inf isLeast_csInf

/- warning: le_cInf_iff' -> le_csInf_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))], (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9392 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9394 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9392 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9394)], (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s)))
Case conversion may be inaccurate. Consider using '#align le_cInf_iff' le_csInf_iff'ₓ'. -/
theorem le_csInf_iff' (hs : s.Nonempty) : b ≤ sInf s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (isLeast_csInf hs).IsGLB
#align le_cInf_iff' le_csInf_iff'

/- warning: Inf_mem -> csInf_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))], (Set.Nonempty.{u1} α s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9447 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9449 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9447 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9449)], (Set.Nonempty.{u1} α s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) s)
Case conversion may be inaccurate. Consider using '#align Inf_mem csInf_memₓ'. -/
theorem csInf_mem (hs : s.Nonempty) : sInf s ∈ s :=
  (isLeast_csInf hs).1
#align Inf_mem csInf_mem

/- warning: infi_mem -> ciInf_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))] [_inst_3 : Nonempty.{u2} ι] (f : ι -> α), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f) (Set.range.{u1, u2} α ι f)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9492 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9494 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9492 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9494)] [_inst_3 : Nonempty.{u2} ι] (f : ι -> α), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f) (Set.range.{u1, u2} α ι f)
Case conversion may be inaccurate. Consider using '#align infi_mem ciInf_memₓ'. -/
theorem ciInf_mem [Nonempty ι] (f : ι → α) : iInf f ∈ range f :=
  csInf_mem (range_nonempty f)
#align infi_mem ciInf_mem

/- warning: monotone_on.map_Inf -> MonotoneOn.map_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))] {β : Type.{u2}} [_inst_3 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (MonotoneOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_3)))) f s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} β (f (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_3) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9546 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9548 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9546 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9548)] {β : Type.{u2}} [_inst_3 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (MonotoneOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_3)))) f s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} β (f (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_3) (Set.image.{u1, u2} α β f s)))
Case conversion may be inaccurate. Consider using '#align monotone_on.map_Inf MonotoneOn.map_csInfₓ'. -/
theorem MonotoneOn.map_csInf {β : Type _} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm
#align monotone_on.map_Inf MonotoneOn.map_csInf

/- warning: monotone.map_Inf -> Monotone.map_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))] {β : Type.{u2}} [_inst_3 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_3)))) f) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} β (f (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_3) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9618 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9620 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9618 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9620)] {β : Type.{u2}} [_inst_3 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_3)))) f) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} β (f (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_3) (Set.image.{u1, u2} α β f s)))
Case conversion may be inaccurate. Consider using '#align monotone.map_Inf Monotone.map_csInfₓ'. -/
theorem Monotone.map_csInf {β : Type _} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm
#align monotone.map_Inf Monotone.map_csInf

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `nonempty`/`set.nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α]

/- warning: cSup_empty -> csSup_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α], Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α], Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cSup_empty csSup_emptyₓ'. -/
@[simp]
theorem csSup_empty : (sSup ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.cSup_empty
#align cSup_empty csSup_empty

/- warning: csupr_of_empty -> ciSup_of_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (iSup.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align csupr_of_empty ciSup_of_emptyₓ'. -/
@[simp]
theorem ciSup_of_empty [IsEmpty ι] (f : ι → α) : (⨆ i, f i) = ⊥ := by
  rw [iSup_of_empty', csSup_empty]
#align csupr_of_empty ciSup_of_empty

/- warning: csupr_false -> ciSup_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : False -> α), Eq.{succ u1} α (iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) False (fun (i : False) => f i)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : False -> α), Eq.{succ u1} α (iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) False (fun (i : False) => f i)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align csupr_false ciSup_falseₓ'. -/
@[simp]
theorem ciSup_false (f : False → α) : (⨆ i, f i) = ⊥ :=
  ciSup_of_empty f
#align csupr_false ciSup_false

/- warning: cInf_univ -> csInf_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α], Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) (Set.univ.{u1} α)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α], Eq.{succ u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) (Set.univ.{u1} α)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cInf_univ csInf_univₓ'. -/
@[simp]
theorem csInf_univ : sInf (univ : Set α) = ⊥ :=
  isLeast_univ.csInf_eq
#align cInf_univ csInf_univ

/- warning: is_lub_cSup' -> isLUB_csSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align is_lub_cSup' isLUB_csSup'ₓ'. -/
theorem isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup s) :=
  by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csSup_empty, isLUB_empty]
  · exact isLUB_csSup hne hs
#align is_lub_cSup' isLUB_csSup'

/- warning: cSup_le_iff' -> csSup_le_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (forall {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) x a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (forall {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) x a)))
Case conversion may be inaccurate. Consider using '#align cSup_le_iff' csSup_le_iff'ₓ'. -/
theorem csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (isLUB_csSup' hs)
#align cSup_le_iff' csSup_le_iff'

/- warning: cSup_le' -> csSup_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a)
Case conversion may be inaccurate. Consider using '#align cSup_le' csSup_le'ₓ'. -/
theorem csSup_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : sSup s ≤ a :=
  (csSup_le_iff' ⟨a, h⟩).2 h
#align cSup_le' csSup_le'

/- warning: le_cSup_iff' -> le_csSup_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_cSup_iff' le_csSup_iff'ₓ'. -/
theorem le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h b hb => le_trans h (csSup_le' hb), fun hb => hb _ fun x => le_csSup h⟩
#align le_cSup_iff' le_csSup_iff'

/- warning: le_csupr_iff' -> le_ciSup_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : ι -> α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u2} α ι s)) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι s)) (forall (b : α), (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (s i) b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {s : ι -> α} {a : α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u1} α ι s)) -> (Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) a (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι s)) (forall (b : α), (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (s i) b) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_csupr_iff' le_ciSup_iff'ₓ'. -/
theorem le_ciSup_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [iSup, h, le_csSup_iff', upperBounds]
#align le_csupr_iff' le_ciSup_iff'

/- warning: le_cInf_iff'' -> le_csInf_iff'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_cInf_iff'' le_csInf_iff''ₓ'. -/
theorem le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a ≤ sInf s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_csInf_iff ⟨⊥, fun a _ => bot_le⟩ Ne
#align le_cInf_iff'' le_csInf_iff''

/- warning: le_cinfi_iff' -> le_ciInf_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (f i))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (f i))
Case conversion may be inaccurate. Consider using '#align le_cinfi_iff' le_ciInf_iff'ₓ'. -/
theorem le_ciInf_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  le_ciInf_iff ⟨⊥, fun a _ => bot_le⟩
#align le_cinfi_iff' le_ciInf_iff'

/- warning: cInf_le' -> csInf_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a)
Case conversion may be inaccurate. Consider using '#align cInf_le' csInf_le'ₓ'. -/
theorem csInf_le' {s : Set α} {a : α} (h : a ∈ s) : sInf s ≤ a :=
  csInf_le ⟨⊥, fun a _ => bot_le⟩ h
#align cInf_le' csInf_le'

/- warning: cinfi_le' -> ciInf_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι f) (f i)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (iInf.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι f) (f i)
Case conversion may be inaccurate. Consider using '#align cinfi_le' ciInf_le'ₓ'. -/
theorem ciInf_le' (f : ι → α) (i : ι) : iInf f ≤ f i :=
  ciInf_le ⟨⊥, fun a _ => bot_le⟩ _
#align cinfi_le' ciInf_le'

/- warning: exists_lt_of_lt_cSup' -> exists_lt_of_lt_csSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) -> (Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) -> (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_lt_cSup' exists_lt_of_lt_csSup'ₓ'. -/
theorem exists_lt_of_lt_csSup' {s : Set α} {a : α} (h : a < sSup s) : ∃ b ∈ s, a < b :=
  by
  contrapose! h
  exact csSup_le' h
#align exists_lt_of_lt_cSup' exists_lt_of_lt_csSup'

/- warning: csupr_le_iff' -> ciSup_le_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u2} α ι f)) -> (forall {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a) (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (f i) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {f : ι -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u1} α ι f)) -> (forall {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι (fun (i : ι) => f i)) a) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align csupr_le_iff' ciSup_le_iff'ₓ'. -/
theorem ciSup_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    (⨆ i, f i) ≤ a ↔ ∀ i, f i ≤ a :=
  (csSup_le_iff' h).trans forall_range_iff
#align csupr_le_iff' ciSup_le_iff'

/- warning: csupr_le' -> ciSup_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (f i) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (f i) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι (fun (i : ι) => f i)) a)
Case conversion may be inaccurate. Consider using '#align csupr_le' ciSup_le'ₓ'. -/
theorem ciSup_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆ i, f i) ≤ a :=
  csSup_le' <| forall_range_iff.2 h
#align csupr_le' ciSup_le'

/- warning: exists_lt_of_lt_csupr' -> exists_lt_of_lt_ciSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {f : ι -> α} {a : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i))) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {f : ι -> α} {a : α}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) a (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι (fun (i : ι) => f i))) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) a (f i)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_lt_csupr' exists_lt_of_lt_ciSup'ₓ'. -/
theorem exists_lt_of_lt_ciSup' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i :=
  by
  contrapose! h
  exact ciSup_le' h
#align exists_lt_of_lt_csupr' exists_lt_of_lt_ciSup'

/- warning: csupr_mono' -> ciSup_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {ι' : Sort.{u3}} {f : ι -> α} {g : ι' -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u3} α ι' g)) -> (forall (i : ι), Exists.{u3} ι' (fun (i' : ι') => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (f i) (g i'))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (iSup.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι f) (iSup.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι' g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {ι' : Sort.{u3}} {f : ι -> α} {g : ι' -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u3} α ι' g)) -> (forall (i : ι), Exists.{u3} ι' (fun (i' : ι') => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (f i) (g i'))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι f) (iSup.{u2, u3} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι' g))
Case conversion may be inaccurate. Consider using '#align csupr_mono' ciSup_mono'ₓ'. -/
theorem ciSup_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  ciSup_le' fun i => Exists.elim (h i) (le_ciSup_of_le hg)
#align csupr_mono' ciSup_mono'

/- warning: cInf_le_cInf' -> csInf_le_csInf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) t))
Case conversion may be inaccurate. Consider using '#align cInf_le_cInf' csInf_le_csInf'ₓ'. -/
theorem csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : sInf s ≤ sInf t :=
  csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂
#align cInf_le_cInf' csInf_le_csInf'

end ConditionallyCompleteLinearOrderBot

namespace WithTop

open Classical

variable [ConditionallyCompleteLinearOrderBot α]

/- warning: with_top.is_lub_Sup' -> WithTop.isLUB_sSup' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : ConditionallyCompleteLattice.{u1} β] {s : Set.{u1} (WithTop.{u1} β)}, (Set.Nonempty.{u1} (WithTop.{u1} β) s) -> (IsLUB.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s (SupSet.sSup.{u1} (WithTop.{u1} β) (WithTop.hasSup.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (ConditionallyCompleteLattice.toHasSup.{u1} β _inst_2)) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : ConditionallyCompleteLattice.{u1} β] {s : Set.{u1} (WithTop.{u1} β)}, (Set.Nonempty.{u1} (WithTop.{u1} β) s) -> (IsLUB.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s (SupSet.sSup.{u1} (WithTop.{u1} β) (instSupSetWithTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align with_top.is_lub_Sup' WithTop.isLUB_sSup'ₓ'. -/
/-- The Sup of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem isLUB_sSup' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply some_le_some.2
      exact le_csSup h_1 ha
    · intro _ _
      exact le_top
  · show ite _ _ _ ∈ _
    split_ifs
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine' some_le_some.2 (csSup_le _ _)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h
        · exact ⟨b, hb⟩
      · intro a ha
        exact some_le_some.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h_1
        use b
        intro a ha
        exact some_le_some.1 (hb ha)
#align with_top.is_lub_Sup' WithTop.isLUB_sSup'

/- warning: with_top.is_lub_Sup -> WithTop.isLUB_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (s : Set.{u1} (WithTop.{u1} α)), IsLUB.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) s (SupSet.sSup.{u1} (WithTop.{u1} α) (WithTop.hasSup.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (s : Set.{u1} (WithTop.{u1} α)), IsLUB.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) s (SupSet.sSup.{u1} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align with_top.is_lub_Sup WithTop.isLUB_sSupₓ'. -/
theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) :=
  by
  cases' s.eq_empty_or_nonempty with hs hs
  · rw [hs]
    show IsLUB ∅ (ite _ _ _)
    split_ifs
    · cases h
    · rw [preimage_empty, csSup_empty]
      exact isLUB_empty
    · exfalso
      apply h_1
      use ⊥
      rintro a ⟨⟩
  exact is_lub_Sup' hs
#align with_top.is_lub_Sup WithTop.isLUB_sSup

/- warning: with_top.is_glb_Inf' -> WithTop.isGLB_sInf' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : ConditionallyCompleteLattice.{u1} β] {s : Set.{u1} (WithTop.{u1} β)}, (BddBelow.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s) -> (IsGLB.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s (InfSet.sInf.{u1} (WithTop.{u1} β) (WithTop.hasInf.{u1} β (ConditionallyCompleteLattice.toHasInf.{u1} β _inst_2)) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : ConditionallyCompleteLattice.{u1} β] {s : Set.{u1} (WithTop.{u1} β)}, (BddBelow.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s) -> (IsGLB.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s (InfSet.sInf.{u1} (WithTop.{u1} β) (instInfSetWithTop.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align with_top.is_glb_Inf' WithTop.isGLB_sInf'ₓ'. -/
/-- The Inf of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem isGLB_sInf' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine' some_le_some.2 (csInf_le _ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff, ← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact some_le_some.1 (hb hc)
  · show ite _ _ _ ∈ _
    split_ifs
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine' some_le_some.2 (le_csInf _ _)
        ·
          classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (h ⟨a, ha⟩).elim
        · intro b hb
          rw [← some_le_some]
          exact ha hb
#align with_top.is_glb_Inf' WithTop.isGLB_sInf'

/- warning: with_top.is_glb_Inf -> WithTop.isGLB_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (s : Set.{u1} (WithTop.{u1} α)), IsGLB.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) s (InfSet.sInf.{u1} (WithTop.{u1} α) (WithTop.hasInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (s : Set.{u1} (WithTop.{u1} α)), IsGLB.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) s (InfSet.sInf.{u1} (WithTop.{u1} α) (instInfSetWithTop.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align with_top.is_glb_Inf WithTop.isGLB_sInfₓ'. -/
theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) :=
  by
  by_cases hs : BddBelow s
  · exact is_glb_Inf' hs
  · exfalso
    apply hs
    use ⊥
    intro _ _
    exact bot_le
#align with_top.is_glb_Inf WithTop.isGLB_sInf

noncomputable instance : CompleteLinearOrder (WithTop α) :=
  { WithTop.linearOrder, WithTop.lattice, WithTop.orderTop,
    WithTop.orderBot with
    sSup := sSup
    le_sup := fun s => (isLUB_sSup s).1
    sup_le := fun s => (isLUB_sSup s).2
    sInf := sInf
    le_inf := fun s => (isGLB_sInf s).2
    inf_le := fun s => (isGLB_sInf s).1 }

/- warning: with_top.coe_Sup -> WithTop.coe_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (iSup.{u1, succ u1} (WithTop.{u1} α) (WithTop.hasSup.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) α (fun (a : α) => iSup.{u1, 0} (WithTop.{u1} α) (WithTop.hasSup.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (iSup.{u1, succ u1} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) α (fun (a : α) => iSup.{u1, 0} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => WithTop.some.{u1} α a))))
Case conversion may be inaccurate. Consider using '#align with_top.coe_Sup WithTop.coe_sSupₓ'. -/
/-- A version of `with_top.coe_Sup'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_Sup' hb, sSup_image]
#align with_top.coe_Sup WithTop.coe_sSup

/- warning: with_top.coe_Inf -> WithTop.coe_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (iInf.{u1, succ u1} (WithTop.{u1} α) (WithTop.hasInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) α (fun (a : α) => iInf.{u1, 0} (WithTop.{u1} α) (WithTop.hasInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (iInf.{u1, succ u1} (WithTop.{u1} α) (instInfSetWithTop.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) α (fun (a : α) => iInf.{u1, 0} (WithTop.{u1} α) (instInfSetWithTop.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => WithTop.some.{u1} α a))))
Case conversion may be inaccurate. Consider using '#align with_top.coe_Inf WithTop.coe_sInfₓ'. -/
/-- A version of `with_top.coe_Inf'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_sInf {s : Set α} (hs : s.Nonempty) : ↑(sInf s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_Inf' hs, sInf_image]
#align with_top.coe_Inf WithTop.coe_sInf

end WithTop

namespace Monotone

variable [Preorder α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`Sup` and `Inf`. -/


/- warning: monotone.le_cSup_image -> Monotone.le_csSup_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α} {c : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) -> (BddAbove.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (f c) (SupSet.sSup.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) f) -> (forall {s : Set.{u2} α} {c : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c s) -> (BddAbove.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (f c) (SupSet.sSup.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.image.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align monotone.le_cSup_image Monotone.le_csSup_imageₓ'. -/
theorem le_csSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ sSup (f '' s) :=
  le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)
#align monotone.le_cSup_image Monotone.le_csSup_image

/- warning: monotone.cSup_image_le -> Monotone.csSup_image_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {B : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) B (upperBounds.{u1} α _inst_1 s)) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (SupSet.sSup.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β f s)) (f B))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) f) -> (forall {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall {B : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) B (upperBounds.{u2} α _inst_1 s)) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (SupSet.sSup.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.image.{u2, u1} α β f s)) (f B))))
Case conversion may be inaccurate. Consider using '#align monotone.cSup_image_le Monotone.csSup_image_leₓ'. -/
theorem csSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    sSup (f '' s) ≤ f B :=
  csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)
#align monotone.cSup_image_le Monotone.csSup_image_le

/- warning: monotone.cInf_image_le -> Monotone.csInf_image_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α} {c : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) -> (BddBelow.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (Set.image.{u1, u2} α β f s)) (f c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) f) -> (forall {s : Set.{u2} α} {c : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c s) -> (BddBelow.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) (Set.image.{u2, u1} α β f s)) (f c)))
Case conversion may be inaccurate. Consider using '#align monotone.cInf_image_le Monotone.csInf_image_leₓ'. -/
theorem csInf_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) :
    sInf (f '' s) ≤ f c :=
  @le_csSup_image αᵒᵈ βᵒᵈ _ _ _ (fun x y hxy => h_mono hxy) _ _ hcs h_bdd
#align monotone.cInf_image_le Monotone.csInf_image_le

/- warning: monotone.le_cInf_image -> Monotone.le_csInf_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {B : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) B (lowerBounds.{u1} α _inst_1 s)) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (f B) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (Set.image.{u1, u2} α β f s)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) f) -> (forall {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall {B : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) B (lowerBounds.{u2} α _inst_1 s)) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (f B) (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) (Set.image.{u2, u1} α β f s)))))
Case conversion may be inaccurate. Consider using '#align monotone.le_cInf_image Monotone.le_csInf_imageₓ'. -/
theorem le_csInf_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ lowerBounds s) :
    f B ≤ sInf (f '' s) :=
  @csSup_image_le αᵒᵈ βᵒᵈ _ _ _ (fun x y hxy => h_mono hxy) _ hs _ hB
#align monotone.le_cInf_image Monotone.le_csInf_image

end Monotone

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

/- warning: galois_connection.l_cSup -> GaloisConnection.l_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (l (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (iSup.{u2, succ u1} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => l ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) l u) -> (forall {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} β (l (SupSet.sSup.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (iSup.{u1, succ u2} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => l (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)))))
Case conversion may be inaccurate. Consider using '#align galois_connection.l_cSup GaloisConnection.l_csSupₓ'. -/
theorem l_csSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne
#align galois_connection.l_cSup GaloisConnection.l_csSup

/- warning: galois_connection.l_cSup' -> GaloisConnection.l_csSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (l (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (SupSet.sSup.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β l s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) l u) -> (forall {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} β (l (SupSet.sSup.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (SupSet.sSup.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.image.{u2, u1} α β l s))))
Case conversion may be inaccurate. Consider using '#align galois_connection.l_cSup' GaloisConnection.l_csSup'ₓ'. -/
theorem l_csSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) := by rw [gc.l_cSup hne hbdd, sSup_image']
#align galois_connection.l_cSup' GaloisConnection.l_csSup'

/- warning: galois_connection.l_csupr -> GaloisConnection.l_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι f)) -> (Eq.{succ u2} β (l (iSup.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i))) (iSup.{u2, u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) ι (fun (i : ι) => l (f i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u1} ι] {l : α -> β} {u : β -> α}, (GaloisConnection.{u3, u2} α β (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {f : ι -> α}, (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.range.{u3, u1} α ι f)) -> (Eq.{succ u2} β (l (iSup.{u3, u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i))) (iSup.{u2, u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) ι (fun (i : ι) => l (f i)))))
Case conversion may be inaccurate. Consider using '#align galois_connection.l_csupr GaloisConnection.l_ciSupₓ'. -/
theorem l_ciSup (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [iSup, gc.l_cSup (range_nonempty _) hf, iSup_range']
#align galois_connection.l_csupr GaloisConnection.l_ciSup

/- warning: galois_connection.l_csupr_set -> GaloisConnection.l_ciSup_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u3} γ} {f : γ -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u3, u1} γ α f s)) -> (Set.Nonempty.{u3} γ s) -> (Eq.{succ u2} β (l (iSup.{u1, succ u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))) (iSup.{u2, succ u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => l (f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u3, u2} α β (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u1} γ} {f : γ -> α}, (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.image.{u1, u3} γ α f s)) -> (Set.Nonempty.{u1} γ s) -> (Eq.{succ u2} β (l (iSup.{u3, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (iSup.{u2, succ u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => l (f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i))))))
Case conversion may be inaccurate. Consider using '#align galois_connection.l_csupr_set GaloisConnection.l_ciSup_setₓ'. -/
theorem l_ciSup_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) :=
  by
  haveI := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_csupr hf
#align galois_connection.l_csupr_set GaloisConnection.l_ciSup_set

/- warning: galois_connection.u_cInf -> GaloisConnection.u_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u2} β}, (Set.Nonempty.{u2} β s) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) s) -> (Eq.{succ u1} α (u (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) s)) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => u ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) l u) -> (forall {s : Set.{u1} β}, (Set.Nonempty.{u1} β s) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) s) -> (Eq.{succ u2} α (u (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) s)) (iInf.{u2, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) (Set.Elem.{u1} β s) (fun (x : Set.Elem.{u1} β s) => u (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) x)))))
Case conversion may be inaccurate. Consider using '#align galois_connection.u_cInf GaloisConnection.u_csInfₓ'. -/
theorem u_csInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = ⨅ x : s, u x :=
  gc.dual.l_csSup hne hbdd
#align galois_connection.u_cInf GaloisConnection.u_csInf

/- warning: galois_connection.u_cInf' -> GaloisConnection.u_csInf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u2} β}, (Set.Nonempty.{u2} β s) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) s) -> (Eq.{succ u1} α (u (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) s)) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.image.{u2, u1} β α u s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) l u) -> (forall {s : Set.{u1} β}, (Set.Nonempty.{u1} β s) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) s) -> (Eq.{succ u2} α (u (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) s)) (InfSet.sInf.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) (Set.image.{u1, u2} β α u s))))
Case conversion may be inaccurate. Consider using '#align galois_connection.u_cInf' GaloisConnection.u_csInf'ₓ'. -/
theorem u_csInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = sInf (u '' s) :=
  gc.dual.l_csSup' hne hbdd
#align galois_connection.u_cInf' GaloisConnection.u_csInf'

/- warning: galois_connection.u_cinfi -> GaloisConnection.u_ciInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {f : ι -> β}, (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (Set.range.{u2, u3} β ι f)) -> (Eq.{succ u1} α (u (iInf.{u2, u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) ι (fun (i : ι) => f i))) (iInf.{u1, u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => u (f i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u1} ι] {l : α -> β} {u : β -> α}, (GaloisConnection.{u3, u2} α β (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {f : ι -> β}, (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (Set.range.{u2, u1} β ι f)) -> (Eq.{succ u3} α (u (iInf.{u2, u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) ι (fun (i : ι) => f i))) (iInf.{u3, u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => u (f i)))))
Case conversion may be inaccurate. Consider using '#align galois_connection.u_cinfi GaloisConnection.u_ciInfₓ'. -/
theorem u_ciInf (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_ciSup hf
#align galois_connection.u_cinfi GaloisConnection.u_ciInf

/- warning: galois_connection.u_cinfi_set -> GaloisConnection.u_ciInf_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u3} γ} {f : γ -> β}, (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (Set.image.{u3, u2} γ β f s)) -> (Set.Nonempty.{u3} γ s) -> (Eq.{succ u1} α (u (iInf.{u2, succ u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))) (iInf.{u1, succ u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => u (f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u3, u2} α β (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u1} γ} {f : γ -> β}, (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (Set.image.{u1, u2} γ β f s)) -> (Set.Nonempty.{u1} γ s) -> (Eq.{succ u3} α (u (iInf.{u2, succ u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (iInf.{u3, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => u (f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i))))))
Case conversion may be inaccurate. Consider using '#align galois_connection.u_cinfi_set GaloisConnection.u_ciInf_setₓ'. -/
theorem u_ciInf_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_ciSup_set hf hne
#align galois_connection.u_cinfi_set GaloisConnection.u_ciInf_set

end GaloisConnection

namespace OrderIso

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

/- warning: order_iso.map_cSup -> OrderIso.map_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (iSup.{u2, succ u1} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] (e : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))))) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (SupSet.sSup.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (iSup.{u1, succ u2} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cSup OrderIso.map_csSupₓ'. -/
theorem map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup hne hbdd
#align order_iso.map_cSup OrderIso.map_csSup

/- warning: order_iso.map_cSup' -> OrderIso.map_csSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (SupSet.sSup.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] (e : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))))) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (SupSet.sSup.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (SupSet.sSup.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e) s)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cSup' OrderIso.map_csSup'ₓ'. -/
theorem map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup' hne hbdd
#align order_iso.map_cSup' OrderIso.map_csSup'

/- warning: order_iso.map_csupr -> OrderIso.map_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι f)) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (iSup.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i))) (iSup.{u2, u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (f i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u1} ι] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {f : ι -> α}, (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.range.{u3, u1} α ι f)) -> (Eq.{succ u2} β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (iSup.{u3, u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i))) (iSup.{u2, u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) ι (fun (i : ι) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (f i))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_csupr OrderIso.map_ciSupₓ'. -/
theorem map_ciSup (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup hf
#align order_iso.map_csupr OrderIso.map_ciSup

/- warning: order_iso.map_csupr_set -> OrderIso.map_ciSup_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u3} γ} {f : γ -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u3, u1} γ α f s)) -> (Set.Nonempty.{u3} γ s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (iSup.{u1, succ u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))) (iSup.{u2, succ u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} γ} {f : γ -> α}, (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.image.{u1, u3} γ α f s)) -> (Set.Nonempty.{u1} γ s) -> (Eq.{succ u2} β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (iSup.{u3, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (iSup.{u2, succ u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_csupr_set OrderIso.map_ciSup_setₓ'. -/
theorem map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set hf hne
#align order_iso.map_csupr_set OrderIso.map_ciSup_set

/- warning: order_iso.map_cInf -> OrderIso.map_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) (iInf.{u2, succ u1} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] (e : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))))) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (InfSet.sInf.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s)) (iInf.{u1, succ u2} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cInf OrderIso.map_csInfₓ'. -/
theorem map_csInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = ⨅ x : s, e x :=
  e.dual.map_csSup hne hbdd
#align order_iso.map_cInf OrderIso.map_csInf

/- warning: order_iso.map_cInf' -> OrderIso.map_csInf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] (e : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))))) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (InfSet.sInf.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s)) (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e) s)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cInf' OrderIso.map_csInf'ₓ'. -/
theorem map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = sInf (e '' s) :=
  e.dual.map_csSup' hne hbdd
#align order_iso.map_cInf' OrderIso.map_csInf'

/- warning: order_iso.map_cinfi -> OrderIso.map_ciInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι f)) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (iInf.{u1, u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => f i))) (iInf.{u2, u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (f i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u1} ι] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {f : ι -> α}, (BddBelow.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.range.{u3, u1} α ι f)) -> (Eq.{succ u2} β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (iInf.{u3, u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => f i))) (iInf.{u2, u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) ι (fun (i : ι) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (f i))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cinfi OrderIso.map_ciInfₓ'. -/
theorem map_ciInf (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_ciSup hf
#align order_iso.map_cinfi OrderIso.map_ciInf

/- warning: order_iso.map_cinfi_set -> OrderIso.map_ciInf_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u3} γ} {f : γ -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u3, u1} γ α f s)) -> (Set.Nonempty.{u3} γ s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (iInf.{u1, succ u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))) (iInf.{u2, succ u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} γ} {f : γ -> α}, (BddBelow.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.image.{u1, u3} γ α f s)) -> (Set.Nonempty.{u1} γ s) -> (Eq.{succ u2} β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (iInf.{u3, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (iInf.{u2, succ u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) e (f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cinfi_set OrderIso.map_ciInf_setₓ'. -/
theorem map_ciInf_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_ciSup_set hf hne
#align order_iso.map_cinfi_set OrderIso.map_ciInf_set

end OrderIso

/-!
### Supremum/infimum of `set.image2`

A collection of lemmas showing what happens to the suprema/infima of `s` and `t` when mapped under
a binary function whose partial evaluations are lower/upper adjoints of Galois connections.
-/


section

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  [ConditionallyCompleteLattice γ] {f : α → β → γ} {s : Set α} {t : Set β}

variable {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

/- warning: cSup_image2_eq_cSup_cSup -> csSup_image2_eq_csSup_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u1, u3} α γ (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (u₁ b)) -> (forall (a : α), GaloisConnection.{u2, u3} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (l a) (u₂ a)) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (SupSet.sSup.{u3} γ (ConditionallyCompleteLattice.toHasSup.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ l s t)) (l (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.sSup.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u2} γ] {s : Set.{u3} α} {t : Set.{u1} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} α γ (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.swap.{succ u3, succ u1, succ u2} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (u₁ b)) -> (forall (a : α), GaloisConnection.{u1, u2} β γ (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (l a) (u₂ a)) -> (Set.Nonempty.{u3} α s) -> (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u2} γ (SupSet.sSup.{u2} γ (ConditionallyCompleteLattice.toSupSet.{u2} γ _inst_3) (Set.image2.{u3, u1, u2} α β γ l s t)) (l (SupSet.sSup.{u3} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) s) (SupSet.sSup.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cSup_image2_eq_cSup_cSup csSup_image2_eq_csSup_csSupₓ'. -/
theorem csSup_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup (image2 l s t) = l (sSup s) (sSup t) :=
  by
  refine' eq_of_forall_ge_iff fun c => _
  rw [csSup_le_iff (hs₁.image2 (fun _ => (h₁ _).monotone_l) (fun _ => (h₂ _).monotone_l) ht₁)
      (hs₀.image2 ht₀),
    forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, csSup_le_iff ht₁ ht₀]
  simp_rw [← (h₂ _).le_iff_le, (h₁ _).le_iff_le, csSup_le_iff hs₁ hs₀]
#align cSup_image2_eq_cSup_cSup csSup_image2_eq_csSup_csSup

/- warning: cSup_image2_eq_cSup_cInf -> csSup_image2_eq_csSup_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u1, u3} α γ (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (u₁ b)) -> (forall (a : α), GaloisConnection.{u2, u3} (OrderDual.{u2} β) γ (OrderDual.preorder.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} β) β γ (l a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β))) (Function.comp.{succ u3, succ u2, succ u2} γ β (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β)) (u₂ a))) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (SupSet.sSup.{u3} γ (ConditionallyCompleteLattice.toHasSup.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ l s t)) (l (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u2} γ] {s : Set.{u3} α} {t : Set.{u1} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} α γ (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.swap.{succ u3, succ u1, succ u2} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (u₁ b)) -> (forall (a : α), GaloisConnection.{u1, u2} (OrderDual.{u1} β) γ (OrderDual.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.comp.{succ u1, succ u1, succ u2} (OrderDual.{u1} β) β γ (l a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β))) (Function.comp.{succ u2, succ u1, succ u1} γ β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) (u₂ a))) -> (Set.Nonempty.{u3} α s) -> (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u2} γ (SupSet.sSup.{u2} γ (ConditionallyCompleteLattice.toSupSet.{u2} γ _inst_3) (Set.image2.{u3, u1, u2} α β γ l s t)) (l (SupSet.sSup.{u3} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) s) (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cSup_image2_eq_cSup_cInf csSup_image2_eq_csSup_csInfₓ'. -/
theorem csSup_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sSup s) (sInf t) :=
  @csSup_image2_eq_csSup_csSup _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cSup_cInf csSup_image2_eq_csSup_csInf

/- warning: cSup_image2_eq_cInf_cSup -> csSup_image2_eq_csInf_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u1, u3} (OrderDual.{u1} α) γ (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} α) α γ (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α))) (Function.comp.{succ u3, succ u1, succ u1} γ α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) (u₁ b))) -> (forall (a : α), GaloisConnection.{u2, u3} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (l a) (u₂ a)) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (SupSet.sSup.{u3} γ (ConditionallyCompleteLattice.toHasSup.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ l s t)) (l (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (SupSet.sSup.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u2} γ] {s : Set.{u3} α} {t : Set.{u1} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} (OrderDual.{u3} α) γ (OrderDual.preorder.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.comp.{succ u3, succ u3, succ u2} (OrderDual.{u3} α) α γ (Function.swap.{succ u3, succ u1, succ u2} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.{u3} α) (fun (_x : OrderDual.{u3} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u3} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.ofDual.{u3} α))) (Function.comp.{succ u2, succ u3, succ u3} γ α (OrderDual.{u3} α) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} α (OrderDual.{u3} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => OrderDual.{u3} α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} α (OrderDual.{u3} α)) (OrderDual.toDual.{u3} α)) (u₁ b))) -> (forall (a : α), GaloisConnection.{u1, u2} β γ (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (l a) (u₂ a)) -> (Set.Nonempty.{u3} α s) -> (BddBelow.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u2} γ (SupSet.sSup.{u2} γ (ConditionallyCompleteLattice.toSupSet.{u2} γ _inst_3) (Set.image2.{u3, u1, u2} α β γ l s t)) (l (InfSet.sInf.{u3} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) s) (SupSet.sSup.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cSup_image2_eq_cInf_cSup csSup_image2_eq_csInf_csSupₓ'. -/
theorem csSup_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sSup (image2 l s t) = l (sInf s) (sSup t) :=
  @csSup_image2_eq_csSup_csSup αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cSup csSup_image2_eq_csInf_csSup

/- warning: cSup_image2_eq_cInf_cInf -> csSup_image2_eq_csInf_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u1, u3} (OrderDual.{u1} α) γ (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} α) α γ (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α))) (Function.comp.{succ u3, succ u1, succ u1} γ α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) (u₁ b))) -> (forall (a : α), GaloisConnection.{u2, u3} (OrderDual.{u2} β) γ (OrderDual.preorder.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} β) β γ (l a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β))) (Function.comp.{succ u3, succ u2, succ u2} γ β (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β)) (u₂ a))) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (SupSet.sSup.{u3} γ (ConditionallyCompleteLattice.toHasSup.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ l s t)) (l (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u2} γ] {s : Set.{u3} α} {t : Set.{u1} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} (OrderDual.{u3} α) γ (OrderDual.preorder.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.comp.{succ u3, succ u3, succ u2} (OrderDual.{u3} α) α γ (Function.swap.{succ u3, succ u1, succ u2} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.{u3} α) (fun (_x : OrderDual.{u3} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u3} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.ofDual.{u3} α))) (Function.comp.{succ u2, succ u3, succ u3} γ α (OrderDual.{u3} α) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} α (OrderDual.{u3} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => OrderDual.{u3} α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} α (OrderDual.{u3} α)) (OrderDual.toDual.{u3} α)) (u₁ b))) -> (forall (a : α), GaloisConnection.{u1, u2} (OrderDual.{u1} β) γ (OrderDual.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.comp.{succ u1, succ u1, succ u2} (OrderDual.{u1} β) β γ (l a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β))) (Function.comp.{succ u2, succ u1, succ u1} γ β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) (u₂ a))) -> (Set.Nonempty.{u3} α s) -> (BddBelow.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u2} γ (SupSet.sSup.{u2} γ (ConditionallyCompleteLattice.toSupSet.{u2} γ _inst_3) (Set.image2.{u3, u1, u2} α β γ l s t)) (l (InfSet.sInf.{u3} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) s) (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cSup_image2_eq_cInf_cInf csSup_image2_eq_csInf_csInfₓ'. -/
theorem csSup_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sInf s) (sInf t) :=
  @csSup_image2_eq_csSup_csSup αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cInf csSup_image2_eq_csInf_csInf

/- warning: cInf_image2_eq_cInf_cInf -> csInf_image2_eq_csInf_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u1} γ α (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (l₁ b) (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b)) -> (forall (a : α), GaloisConnection.{u3, u2} γ β (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (l₂ a) (u a)) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.sInf.{u3} γ (ConditionallyCompleteLattice.toHasInf.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ u s t)) (u (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u2} α} {t : Set.{u1} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} γ α (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (l₁ b) (Function.swap.{succ u2, succ u1, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b)) -> (forall (a : α), GaloisConnection.{u3, u1} γ β (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (l₂ a) (u a)) -> (Set.Nonempty.{u2} α s) -> (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.sInf.{u3} γ (ConditionallyCompleteLattice.toInfSet.{u3} γ _inst_3) (Set.image2.{u2, u1, u3} α β γ u s t)) (u (InfSet.sInf.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s) (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cInf_image2_eq_cInf_cInf csInf_image2_eq_csInf_csInfₓ'. -/
theorem csInf_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sInf s) (sInf t) :=
  @csSup_image2_eq_csSup_csSup αᵒᵈ βᵒᵈ γᵒᵈ _ _ _ _ _ _ l₁ l₂ (fun _ => (h₁ _).dual) fun _ =>
    (h₂ _).dual
#align cInf_image2_eq_cInf_cInf csInf_image2_eq_csInf_csInf

/- warning: cInf_image2_eq_cInf_cSup -> csInf_image2_eq_csInf_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u1} γ α (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (l₁ b) (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b)) -> (forall (a : α), GaloisConnection.{u3, u2} γ (OrderDual.{u2} β) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (Function.comp.{succ u3, succ u2, succ u2} γ β (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β)) (l₂ a)) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} β) β γ (u a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β)))) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.sInf.{u3} γ (ConditionallyCompleteLattice.toHasInf.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ u s t)) (u (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (SupSet.sSup.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u2} α} {t : Set.{u1} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} γ α (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (l₁ b) (Function.swap.{succ u2, succ u1, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b)) -> (forall (a : α), GaloisConnection.{u3, u1} γ (OrderDual.{u1} β) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (Function.comp.{succ u3, succ u1, succ u1} γ β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) (l₂ a)) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} β) β γ (u a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β)))) -> (Set.Nonempty.{u2} α s) -> (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.sInf.{u3} γ (ConditionallyCompleteLattice.toInfSet.{u3} γ _inst_3) (Set.image2.{u2, u1, u3} α β γ u s t)) (u (InfSet.sInf.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s) (SupSet.sSup.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cInf_image2_eq_cInf_cSup csInf_image2_eq_csInf_csSupₓ'. -/
theorem csInf_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sInf s) (sSup t) :=
  @csInf_image2_eq_csInf_csInf _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cInf_cSup csInf_image2_eq_csInf_csSup

/- warning: cInf_image2_eq_cSup_cInf -> csInf_image2_eq_csSup_csInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u1} γ (OrderDual.{u1} α) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Function.comp.{succ u3, succ u1, succ u1} γ α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) (l₁ b)) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} α) α γ (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)))) -> (forall (a : α), GaloisConnection.{u3, u2} γ β (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (l₂ a) (u a)) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.sInf.{u3} γ (ConditionallyCompleteLattice.toHasInf.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ u s t)) (u (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (InfSet.sInf.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u2} α} {t : Set.{u1} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} γ (OrderDual.{u2} α) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Function.comp.{succ u3, succ u2, succ u2} γ α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) (l₁ b)) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} α) α γ (Function.swap.{succ u2, succ u1, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α)))) -> (forall (a : α), GaloisConnection.{u3, u1} γ β (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (l₂ a) (u a)) -> (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.sInf.{u3} γ (ConditionallyCompleteLattice.toInfSet.{u3} γ _inst_3) (Set.image2.{u2, u1, u3} α β γ u s t)) (u (SupSet.sSup.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s) (InfSet.sInf.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cInf_image2_eq_cSup_cInf csInf_image2_eq_csSup_csInfₓ'. -/
theorem csInf_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sSup s) (sInf t) :=
  @csInf_image2_eq_csInf_csInf αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cInf csInf_image2_eq_csSup_csInf

/- warning: cInf_image2_eq_cSup_cSup -> csInf_image2_eq_csSup_csSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u1} γ (OrderDual.{u1} α) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Function.comp.{succ u3, succ u1, succ u1} γ α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) (l₁ b)) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} α) α γ (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)))) -> (forall (a : α), GaloisConnection.{u3, u2} γ (OrderDual.{u2} β) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (Function.comp.{succ u3, succ u2, succ u2} γ β (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β)) (l₂ a)) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} β) β γ (u a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β)))) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.sInf.{u3} γ (ConditionallyCompleteLattice.toHasInf.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ u s t)) (u (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.sSup.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u2} α} {t : Set.{u1} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} γ (OrderDual.{u2} α) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Function.comp.{succ u3, succ u2, succ u2} γ α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) (l₁ b)) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} α) α γ (Function.swap.{succ u2, succ u1, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α)))) -> (forall (a : α), GaloisConnection.{u3, u1} γ (OrderDual.{u1} β) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (Function.comp.{succ u3, succ u1, succ u1} γ β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) (l₂ a)) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} β) β γ (u a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β)))) -> (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.sInf.{u3} γ (ConditionallyCompleteLattice.toInfSet.{u3} γ _inst_3) (Set.image2.{u2, u1, u3} α β γ u s t)) (u (SupSet.sSup.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s) (SupSet.sSup.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cInf_image2_eq_cSup_cSup csInf_image2_eq_csSup_csSupₓ'. -/
theorem csInf_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sSup s) (sSup t) :=
  @csInf_image2_eq_csInf_csInf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cSup csInf_image2_eq_csSup_csSup

end

section WithTopBot

/-!
### Complete lattice structure on `with_top (with_bot α)`

If `α` is a `conditionally_complete_lattice`, then we show that `with_top α` and `with_bot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `with_top (with_bot α)` and `with_bot (with_top α)` naturally inherit the structure of a
complete lattice. Note that for `α` a conditionally complete lattice, `Sup` and `Inf` both return
junk values for sets which are empty or unbounded. The extension of `Sup` to `with_top α` fixes
the unboundedness problem and the extension to `with_bot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals `[-∞, ∞]` are a complete linear order.
-/


open Classical

#print WithTop.conditionallyCompleteLattice /-
/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type _}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) :=
  { WithTop.lattice, WithTop.hasSup,
    WithTop.hasInf with
    le_cSup := fun S a hS haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS
    cSup_le := fun S a hS haS => (WithTop.isLUB_sSup' hS).2 haS
    cInf_le := fun S a hS haS => (WithTop.isGLB_sInf' hS).1 haS
    le_cInf := fun S a hS haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS }
#align with_top.conditionally_complete_lattice WithTop.conditionallyCompleteLattice
-/

#print WithBot.conditionallyCompleteLattice /-
/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithBot.conditionallyCompleteLattice {α : Type _}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithBot α) :=
  { WithBot.lattice, WithBot.hasSup,
    WithBot.hasInf with
    le_cSup := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).cInf_le
    cSup_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_cInf
    cInf_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_cSup
    le_cInf := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).cSup_le }
#align with_bot.conditionally_complete_lattice WithBot.conditionallyCompleteLattice
-/

#print WithTop.WithBot.completeLattice /-
noncomputable instance WithTop.WithBot.completeLattice {α : Type _}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) :=
  { WithTop.hasInf, WithTop.hasSup, WithTop.boundedOrder,
    WithTop.lattice with
    le_sup := fun S a haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS
    sup_le := fun S a ha => by
      cases' S.eq_empty_or_nonempty with h
      · show ite _ _ _ ≤ a
        split_ifs
        · rw [h] at h_1
          cases h_1
        · convert bot_le
          convert WithBot.csSup_empty
          rw [h]
          rfl
        · exfalso
          apply h_2
          use ⊥
          rw [h]
          rintro b ⟨⟩
      · refine' (WithTop.isLUB_sSup' h).2 ha
    inf_le := fun S a haS =>
      show ite _ _ _ ≤ a by
        split_ifs
        · cases' a with a
          exact le_rfl
          cases h haS <;> tauto
        · cases a
          · exact le_top
          · apply WithTop.some_le_some.2
            refine' csInf_le _ haS
            use ⊥
            intro b hb
            exact bot_le
    le_inf := fun S a haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS }
#align with_top.with_bot.complete_lattice WithTop.WithBot.completeLattice
-/

#print WithTop.WithBot.completeLinearOrder /-
noncomputable instance WithTop.WithBot.completeLinearOrder {α : Type _}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithTop (WithBot α)) :=
  { WithTop.WithBot.completeLattice, WithTop.linearOrder with }
#align with_top.with_bot.complete_linear_order WithTop.WithBot.completeLinearOrder
-/

#print WithBot.WithTop.completeLattice /-
noncomputable instance WithBot.WithTop.completeLattice {α : Type _}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithBot (WithTop α)) :=
  { WithBot.hasInf, WithBot.hasSup, WithBot.boundedOrder,
    WithBot.lattice with
    le_sup := (@WithTop.WithBot.completeLattice αᵒᵈ _).inf_le
    sup_le := (@WithTop.WithBot.completeLattice αᵒᵈ _).le_inf
    inf_le := (@WithTop.WithBot.completeLattice αᵒᵈ _).le_sup
    le_inf := (@WithTop.WithBot.completeLattice αᵒᵈ _).sup_le }
#align with_bot.with_top.complete_lattice WithBot.WithTop.completeLattice
-/

#print WithBot.WithTop.completeLinearOrder /-
noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type _}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) :=
  { WithBot.WithTop.completeLattice, WithBot.linearOrder with }
#align with_bot.with_top.complete_linear_order WithBot.WithTop.completeLinearOrder
-/

/- warning: with_top.supr_coe_eq_top -> WithTop.iSup_coe_eq_top is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] (f : ι -> α), Iff (Eq.{succ u2} (WithTop.{u2} α) (iSup.{u2, u1} (WithTop.{u2} α) (WithTop.hasSup.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))) ι (fun (x : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) α (WithTop.{u2} α) (HasLiftT.mk.{succ u2, succ u2} α (WithTop.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} α (WithTop.{u2} α) (WithTop.hasCoeT.{u2} α))) (f x))) (Top.top.{u2} (WithTop.{u2} α) (WithTop.hasTop.{u2} α))) (Not (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u1} α ι f)))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : ι -> α), Iff (Eq.{succ u1} (WithTop.{u1} α) (iSup.{u1, u2} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) ι (fun (x : ι) => WithTop.some.{u1} α (f x))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (Not (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u2} α ι f)))
Case conversion may be inaccurate. Consider using '#align with_top.supr_coe_eq_top WithTop.iSup_coe_eq_topₓ'. -/
theorem WithTop.iSup_coe_eq_top {ι : Sort _} {α : Type _} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : (⨆ x, (f x : WithTop α)) = ⊤ ↔ ¬BddAbove (Set.range f) :=
  by
  rw [iSup_eq_top, not_bddAbove_iff]
  refine' ⟨fun hf r => _, fun hf a ha => _⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, with_top.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using with_top.coe_lt_coe.mpr hi⟩
#align with_top.supr_coe_eq_top WithTop.iSup_coe_eq_top

/- warning: with_top.supr_coe_lt_top -> WithTop.iSup_coe_lt_top is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] (f : ι -> α), Iff (LT.lt.{u2} (WithTop.{u2} α) (Preorder.toHasLt.{u2} (WithTop.{u2} α) (WithTop.preorder.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))))) (iSup.{u2, u1} (WithTop.{u2} α) (WithTop.hasSup.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))) ι (fun (x : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) α (WithTop.{u2} α) (HasLiftT.mk.{succ u2, succ u2} α (WithTop.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} α (WithTop.{u2} α) (WithTop.hasCoeT.{u2} α))) (f x))) (Top.top.{u2} (WithTop.{u2} α) (WithTop.hasTop.{u2} α))) (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u1} α ι f))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : ι -> α), Iff (LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))))) (iSup.{u1, u2} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) ι (fun (x : ι) => WithTop.some.{u1} α (f x))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u2} α ι f))
Case conversion may be inaccurate. Consider using '#align with_top.supr_coe_lt_top WithTop.iSup_coe_lt_topₓ'. -/
theorem WithTop.iSup_coe_lt_top {ι : Sort _} {α : Type _} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : (⨆ x, (f x : WithTop α)) < ⊤ ↔ BddAbove (Set.range f) :=
  lt_top_iff_ne_top.trans <| (WithTop.iSup_coe_eq_top f).Not.trans Classical.not_not
#align with_top.supr_coe_lt_top WithTop.iSup_coe_lt_top

end WithTopBot

-- Guard against import creep
assert_not_exists Multiset

