/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.basic
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
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
    if ⊤ ∈ S then ⊤ else if BddAbove (coe ⁻¹' S : Set α) then ↑(supₛ (coe ⁻¹' S : Set α)) else ⊤⟩

noncomputable instance {α : Type _} [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} then ⊤ else ↑(infₛ (coe ⁻¹' S : Set α))⟩

noncomputable instance {α : Type _} [SupSet α] : SupSet (WithBot α) :=
  ⟨(@WithTop.hasInf αᵒᵈ _).infₛ⟩

noncomputable instance {α : Type _} [Preorder α] [InfSet α] : InfSet (WithBot α) :=
  ⟨(@WithTop.hasSup αᵒᵈ _ _).supₛ⟩

#print WithTop.infₛ_empty /-
@[simp]
theorem WithTop.infₛ_empty {α : Type _} [InfSet α] : infₛ (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| Set.empty_subset _
#align with_top.cInf_empty WithTop.infₛ_empty
-/

#print WithTop.infᵢ_empty /-
@[simp]
theorem WithTop.infᵢ_empty {α : Type _} [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    (⨅ i, f i) = ⊤ := by rw [infᵢ, range_eq_empty, WithTop.infₛ_empty]
#align with_top.cinfi_empty WithTop.infᵢ_empty
-/

#print WithTop.coe_infₛ' /-
theorem WithTop.coe_infₛ' [InfSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(infₛ s) = (infₛ (coe '' s) : WithTop α) :=
  by
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs
  · cases h (mem_image_of_mem _ hx)
  · rw [preimage_image_eq]
    exact Option.some_injective _
#align with_top.coe_Inf' WithTop.coe_infₛ'
-/

#print WithTop.coe_infᵢ /-
@[norm_cast]
theorem WithTop.coe_infᵢ [Nonempty ι] [InfSet α] (f : ι → α) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [infᵢ, infᵢ, WithTop.coe_infₛ' (range_nonempty f), range_comp]
#align with_top.coe_infi WithTop.coe_infᵢ
-/

#print WithTop.coe_supₛ' /-
theorem WithTop.coe_supₛ' [Preorder α] [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(supₛ s) = (supₛ (coe '' s) : WithTop α) :=
  by
  change _ = ite _ _ _
  rw [if_neg, preimage_image_eq, if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, h, ⟨⟩⟩
#align with_top.coe_Sup' WithTop.coe_supₛ'
-/

/- warning: with_top.coe_supr -> WithTop.coe_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : SupSet.{u1} α] (f : ι -> α), (BddAbove.{u1} α _inst_1 (Set.range.{u1, u2} α ι f)) -> (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (supᵢ.{u1, u2} α _inst_2 ι (fun (i : ι) => f i))) (supᵢ.{u1, u2} (WithTop.{u1} α) (WithTop.hasSup.{u1} α _inst_1 _inst_2) ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : SupSet.{u2} α] (f : ι -> α), (BddAbove.{u2} α _inst_1 (Set.range.{u2, u1} α ι f)) -> (Eq.{succ u2} (WithTop.{u2} α) (WithTop.some.{u2} α (supᵢ.{u2, u1} α _inst_2 ι (fun (i : ι) => f i))) (supᵢ.{u2, u1} (WithTop.{u2} α) (instSupSetWithTop.{u2} α _inst_1 _inst_2) ι (fun (i : ι) => WithTop.some.{u2} α (f i))))
Case conversion may be inaccurate. Consider using '#align with_top.coe_supr WithTop.coe_supᵢₓ'. -/
@[norm_cast]
theorem WithTop.coe_supᵢ [Preorder α] [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by rw [supᵢ, supᵢ, WithTop.coe_supₛ' h, range_comp]
#align with_top.coe_supr WithTop.coe_supᵢ

/- warning: with_bot.cSup_empty -> WithBot.supₛ_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (WithBot.{u1} α) (SupSet.supₛ.{u1} (WithBot.{u1} α) (WithBot.hasSup.{u1} α _inst_1) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (WithBot.{u1} α)) (Set.hasEmptyc.{u1} (WithBot.{u1} α)))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (WithBot.{u1} α) (SupSet.supₛ.{u1} (WithBot.{u1} α) (instSupSetWithBot.{u1} α _inst_1) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (WithBot.{u1} α)) (Set.instEmptyCollectionSet.{u1} (WithBot.{u1} α)))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))
Case conversion may be inaccurate. Consider using '#align with_bot.cSup_empty WithBot.supₛ_emptyₓ'. -/
@[simp]
theorem WithBot.supₛ_empty {α : Type _} [SupSet α] : supₛ (∅ : Set (WithBot α)) = ⊥ :=
  if_pos <| Set.empty_subset _
#align with_bot.cSup_empty WithBot.supₛ_empty

/- warning: with_bot.csupr_empty -> WithBot.supᵢ_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : IsEmpty.{u1} ι] [_inst_2 : SupSet.{u2} α] (f : ι -> (WithBot.{u2} α)), Eq.{succ u2} (WithBot.{u2} α) (supᵢ.{u2, u1} (WithBot.{u2} α) (WithBot.hasSup.{u2} α _inst_2) ι (fun (i : ι) => f i)) (Bot.bot.{u2} (WithBot.{u2} α) (WithBot.hasBot.{u2} α))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : IsEmpty.{u1} ι] [_inst_2 : SupSet.{u2} α] (f : ι -> (WithBot.{u2} α)), Eq.{succ u2} (WithBot.{u2} α) (supᵢ.{u2, u1} (WithBot.{u2} α) (instSupSetWithBot.{u2} α _inst_2) ι (fun (i : ι) => f i)) (Bot.bot.{u2} (WithBot.{u2} α) (WithBot.bot.{u2} α))
Case conversion may be inaccurate. Consider using '#align with_bot.csupr_empty WithBot.supᵢ_emptyₓ'. -/
@[simp]
theorem WithBot.supᵢ_empty {α : Type _} [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    (⨆ i, f i) = ⊥ :=
  @WithTop.infᵢ_empty _ αᵒᵈ _ _ _
#align with_bot.csupr_empty WithBot.supᵢ_empty

/- warning: with_bot.coe_Sup' -> WithBot.coe_supₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (SupSet.supₛ.{u1} α _inst_1 s)) (SupSet.supₛ.{u1} (WithBot.{u1} α) (WithBot.hasSup.{u1} α _inst_1) (Set.image.{u1, u1} α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (SupSet.supₛ.{u1} α _inst_1 s)) (SupSet.supₛ.{u1} (WithBot.{u1} α) (instSupSetWithBot.{u1} α _inst_1) (Set.image.{u1, u1} α (WithBot.{u1} α) (fun (a : α) => WithBot.some.{u1} α a) s)))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_Sup' WithBot.coe_supₛ'ₓ'. -/
@[norm_cast]
theorem WithBot.coe_supₛ' [SupSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(supₛ s) = (supₛ (coe '' s) : WithBot α) :=
  @WithTop.coe_infₛ' αᵒᵈ _ _ hs
#align with_bot.coe_Sup' WithBot.coe_supₛ'

/- warning: with_bot.coe_supr -> WithBot.coe_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : SupSet.{u1} α] (f : ι -> α), Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (supᵢ.{u1, u2} α _inst_2 ι (fun (i : ι) => f i))) (supᵢ.{u1, u2} (WithBot.{u1} α) (WithBot.hasSup.{u1} α _inst_2) ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : SupSet.{u1} α] (f : ι -> α), Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (supᵢ.{u1, u2} α _inst_2 ι (fun (i : ι) => f i))) (supᵢ.{u1, u2} (WithBot.{u1} α) (instSupSetWithBot.{u1} α _inst_2) ι (fun (i : ι) => WithBot.some.{u1} α (f i)))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_supr WithBot.coe_supᵢₓ'. -/
@[norm_cast]
theorem WithBot.coe_supᵢ [Nonempty ι] [SupSet α] (f : ι → α) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  @WithTop.coe_infᵢ αᵒᵈ _ _ _ _
#align with_bot.coe_supr WithBot.coe_supᵢ

/- warning: with_bot.coe_Inf' -> WithBot.coe_infₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : InfSet.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α _inst_1 s) -> (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (InfSet.infₛ.{u1} α _inst_2 s)) (InfSet.infₛ.{u1} (WithBot.{u1} α) (WithBot.hasInf.{u1} α _inst_1 _inst_2) (Set.image.{u1, u1} α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : InfSet.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α _inst_1 s) -> (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (InfSet.infₛ.{u1} α _inst_2 s)) (InfSet.infₛ.{u1} (WithBot.{u1} α) (instInfSetWithBot.{u1} α _inst_1 _inst_2) (Set.image.{u1, u1} α (WithBot.{u1} α) (fun (a : α) => WithBot.some.{u1} α a) s)))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_Inf' WithBot.coe_infₛ'ₓ'. -/
@[norm_cast]
theorem WithBot.coe_infₛ' [Preorder α] [InfSet α] {s : Set α} (hs : BddBelow s) :
    ↑(infₛ s) = (infₛ (coe '' s) : WithBot α) :=
  @WithTop.coe_supₛ' αᵒᵈ _ _ _ hs
#align with_bot.coe_Inf' WithBot.coe_infₛ'

/- warning: with_bot.coe_infi -> WithBot.coe_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : InfSet.{u1} α] (f : ι -> α), (BddBelow.{u1} α _inst_1 (Set.range.{u1, u2} α ι f)) -> (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (infᵢ.{u1, u2} α _inst_2 ι (fun (i : ι) => f i))) (infᵢ.{u1, u2} (WithBot.{u1} α) (WithBot.hasInf.{u1} α _inst_1 _inst_2) ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : InfSet.{u2} α] (f : ι -> α), (BddBelow.{u2} α _inst_1 (Set.range.{u2, u1} α ι f)) -> (Eq.{succ u2} (WithBot.{u2} α) (WithBot.some.{u2} α (infᵢ.{u2, u1} α _inst_2 ι (fun (i : ι) => f i))) (infᵢ.{u2, u1} (WithBot.{u2} α) (instInfSetWithBot.{u2} α _inst_1 _inst_2) ι (fun (i : ι) => WithBot.some.{u2} α (f i))))
Case conversion may be inaccurate. Consider using '#align with_bot.coe_infi WithBot.coe_infᵢₓ'. -/
@[norm_cast]
theorem WithBot.coe_infᵢ [Preorder α] [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  @WithTop.coe_supᵢ αᵒᵈ _ _ _ _ h
#align with_bot.coe_infi WithBot.coe_infᵢ

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
/- ./././Mathport/Syntax/Translate/Command.lean:417:11: unsupported: advanced extends in structure -/
/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrder (α : Type _) extends ConditionallyCompleteLattice α,
  "./././Mathport/Syntax/Translate/Command.lean:417:11: unsupported: advanced extends in structure"
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
  supₛ_empty : Sup ∅ = ⊥
#align conditionally_complete_linear_order_bot ConditionallyCompleteLinearOrderBot
-/

#print ConditionallyCompleteLinearOrderBot.toOrderBot /-
-- see Note [lower instance priority]
instance (priority := 100) ConditionallyCompleteLinearOrderBot.toOrderBot
    [h : ConditionallyCompleteLinearOrderBot α] : OrderBot α :=
  { h with }
#align conditionally_complete_linear_order_bot.to_order_bot ConditionallyCompleteLinearOrderBot.toOrderBot
-/

#print CompleteLattice.toConditionallyCompleteLattice /-
-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α :=
  {
    ‹CompleteLattice
        α› with
    le_cSup := by intros <;> apply le_supₛ <;> assumption
    cSup_le := by intros <;> apply supₛ_le <;> assumption
    cInf_le := by intros <;> apply infₛ_le <;> assumption
    le_cInf := by intros <;> apply le_infₛ <;> assumption }
#align complete_lattice.to_conditionally_complete_lattice CompleteLattice.toConditionallyCompleteLattice
-/

#print CompleteLinearOrder.toConditionallyCompleteLinearOrderBot /-
-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type _}
    [CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α :=
  { CompleteLattice.toConditionallyCompleteLattice, ‹CompleteLinearOrder α› with
    supₛ_empty := supₛ_empty }
#align complete_linear_order.to_conditionally_complete_linear_order_bot CompleteLinearOrder.toConditionallyCompleteLinearOrderBot
-/

section

open Classical

#print IsWellOrder.conditionallyCompleteLinearOrderBot /-
/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible]
noncomputable def IsWellOrder.conditionallyCompleteLinearOrderBot (α : Type _) [i₁ : LinearOrder α]
    [i₂ : OrderBot α] [h : IsWellOrder α (· < ·)] : ConditionallyCompleteLinearOrderBot α :=
  { i₁, i₂,
    LinearOrder.toLattice with
    infₛ := fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥
    cInf_le := fun s a hs has => by
      have s_ne : s.nonempty := ⟨a, has⟩
      simpa [s_ne] using not_lt.1 (h.wf.not_lt_min s s_ne has)
    le_cInf := fun s a hs has => by
      simp only [hs, dif_pos]
      exact has (h.wf.min_mem s hs)
    supₛ := fun s => if hs : (upperBounds s).Nonempty then h.wf.min _ hs else ⊥
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
    supₛ_empty := by simpa using eq_bot_iff.2 (not_lt.1 <| h.wf.not_lt_min _ _ <| mem_univ ⊥) }
#align is_well_order.conditionally_complete_linear_order_bot IsWellOrder.conditionallyCompleteLinearOrderBot
-/

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

#print conditionallyCompleteLatticeOfSupₛ /-
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
def conditionallyCompleteLatticeOfSupₛ (α : Type _) [H1 : PartialOrder α] [H2 : SupSet α]
    (bdd_above_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bdd_below_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (is_lub_Sup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (supₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with
    sup := fun a b => supₛ {a, b}
    le_sup_left := fun a b =>
      (isLUB_supₛ {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    le_sup_right := fun a b =>
      (isLUB_supₛ {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    sup_le := fun a b c hac hbc =>
      (isLUB_supₛ {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    inf := fun a b => supₛ (lowerBounds {a, b})
    inf_le_left := fun a b =>
      (isLUB_supₛ (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bdd_below_pair a b)).2
        fun c hc => hc <| mem_insert _ _
    inf_le_right := fun a b =>
      (isLUB_supₛ (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bdd_below_pair a b)).2
        fun c hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    le_inf := fun c a b hca hcb =>
      (isLUB_supₛ (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hcb) hca⟩).1
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    infₛ := fun s => supₛ (lowerBounds s)
    cSup_le := fun s a hs ha => (isLUB_supₛ s ⟨a, ha⟩ hs).2 ha
    le_cSup := fun s a hs ha => (isLUB_supₛ s hs ⟨a, ha⟩).1 ha
    cInf_le := fun s a hs ha =>
      (isLUB_supₛ (lowerBounds s) (Nonempty.bddAbove_lowerBounds ⟨a, ha⟩) hs).2 fun b hb => hb ha
    le_cInf := fun s a hs ha => (isLUB_supₛ (lowerBounds s) hs.bddAbove_lowerBounds ⟨a, ha⟩).1 ha }
#align conditionally_complete_lattice_of_Sup conditionallyCompleteLatticeOfSupₛ
-/

#print conditionallyCompleteLatticeOfInfₛ /-
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
def conditionallyCompleteLatticeOfInfₛ (α : Type _) [H1 : PartialOrder α] [H2 : InfSet α]
    (bdd_above_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bdd_below_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (is_glb_Inf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (infₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with
    inf := fun a b => infₛ {a, b}
    inf_le_left := fun a b =>
      (isGLB_infₛ {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    inf_le_right := fun a b =>
      (isGLB_infₛ {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    le_inf := fun c a b hca hcb =>
      (isGLB_infₛ {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    sup := fun a b => infₛ (upperBounds {a, b})
    le_sup_left := fun a b =>
      (isGLB_infₛ (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bdd_above_pair a b)).2
        fun c hc => hc <| mem_insert _ _
    le_sup_right := fun a b =>
      (isGLB_infₛ (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bdd_above_pair a b)).2
        fun c hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    sup_le := fun a b c hac hbc =>
      (isGLB_infₛ (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hbc) hac⟩).1
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    supₛ := fun s => infₛ (upperBounds s)
    le_cInf := fun s a hs ha => (isGLB_infₛ s ⟨a, ha⟩ hs).2 ha
    cInf_le := fun s a hs ha => (isGLB_infₛ s hs ⟨a, ha⟩).1 ha
    le_cSup := fun s a hs ha =>
      (isGLB_infₛ (upperBounds s) (Nonempty.bddBelow_upperBounds ⟨a, ha⟩) hs).2 fun b hb => hb ha
    cSup_le := fun s a hs ha => (isGLB_infₛ (upperBounds s) hs.bddBelow_upperBounds ⟨a, ha⟩).1 ha }
#align conditionally_complete_lattice_of_Inf conditionallyCompleteLatticeOfInfₛ
-/

#print conditionallyCompleteLatticeOfLatticeOfSupₛ /-
/-- A version of `conditionally_complete_lattice_of_Sup` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `Inf` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfSupₛ (α : Type _) [H1 : Lattice α] [H2 : SupSet α]
    (is_lub_Sup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (supₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfSupₛ α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isLUB_supₛ with }
#align conditionally_complete_lattice_of_lattice_of_Sup conditionallyCompleteLatticeOfLatticeOfSupₛ
-/

#print conditionallyCompleteLatticeOfLatticeOfInfₛ /-
/-- A version of `conditionally_complete_lattice_of_Inf` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `Sup` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfInfₛ (α : Type _) [H1 : Lattice α] [H2 : InfSet α]
    (is_glb_Inf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (infₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfInfₛ α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isGLB_infₛ with }
#align conditionally_complete_lattice_of_lattice_of_Inf conditionallyCompleteLatticeOfLatticeOfInfₛ
-/

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

/- warning: le_cSup -> le_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_cSup le_csupₛₓ'. -/
theorem le_csupₛ (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ supₛ s :=
  ConditionallyCompleteLattice.le_cSup s a h₁ h₂
#align le_cSup le_csupₛ

/- warning: cSup_le -> csupₛ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align cSup_le csupₛ_leₓ'. -/
theorem csupₛ_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : supₛ s ≤ a :=
  ConditionallyCompleteLattice.cSup_le s a h₁ h₂
#align cSup_le csupₛ_le

/- warning: cInf_le -> cinfₛ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align cInf_le cinfₛ_leₓ'. -/
theorem cinfₛ_le (h₁ : BddBelow s) (h₂ : a ∈ s) : infₛ s ≤ a :=
  ConditionallyCompleteLattice.cInf_le s a h₁ h₂
#align cInf_le cinfₛ_le

/- warning: le_cInf -> le_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_cInf le_cinfₛₓ'. -/
theorem le_cinfₛ (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ infₛ s :=
  ConditionallyCompleteLattice.le_cInf s a h₁ h₂
#align le_cInf le_cinfₛ

/- warning: le_cSup_of_le -> le_csupₛ_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_cSup_of_le le_csupₛ_of_leₓ'. -/
theorem le_csupₛ_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ supₛ s :=
  le_trans h (le_csupₛ hs hb)
#align le_cSup_of_le le_csupₛ_of_le

/- warning: cInf_le_of_le -> cinfₛ_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align cInf_le_of_le cinfₛ_le_of_leₓ'. -/
theorem cinfₛ_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : infₛ s ≤ a :=
  le_trans (cinfₛ_le hs hb) h
#align cInf_le_of_le cinfₛ_le_of_le

/- warning: cSup_le_cSup -> csupₛ_le_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align cSup_le_cSup csupₛ_le_csupₛₓ'. -/
theorem csupₛ_le_csupₛ (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : supₛ s ≤ supₛ t :=
  csupₛ_le hs fun a ha => le_csupₛ ht (h ha)
#align cSup_le_cSup csupₛ_le_csupₛ

/- warning: cInf_le_cInf -> cinfₛ_le_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) t) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) t) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align cInf_le_cInf cinfₛ_le_cinfₛₓ'. -/
theorem cinfₛ_le_cinfₛ (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : infₛ t ≤ infₛ s :=
  le_cinfₛ hs fun a ha => cinfₛ_le ht (h ha)
#align cInf_le_cInf cinfₛ_le_cinfₛ

/- warning: le_cSup_iff -> le_csupₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_cSup_iff le_csupₛ_iffₓ'. -/
theorem le_csupₛ_iff (h : BddAbove s) (hs : s.Nonempty) :
    a ≤ supₛ s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h b hb => le_trans h (csupₛ_le hs hb), fun hb => hb _ fun x => le_csupₛ h⟩
#align le_cSup_iff le_csupₛ_iff

/- warning: cInf_le_iff -> cinfₛ_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)))
Case conversion may be inaccurate. Consider using '#align cInf_le_iff cinfₛ_le_iffₓ'. -/
theorem cinfₛ_le_iff (h : BddBelow s) (hs : s.Nonempty) : infₛ s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h b hb => le_trans (le_cinfₛ hs hb) h, fun hb => hb _ fun x => cinfₛ_le h⟩
#align cInf_le_iff cinfₛ_le_iff

/- warning: is_lub_cSup -> isLUB_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align is_lub_cSup isLUB_csupₛₓ'. -/
theorem isLUB_csupₛ (ne : s.Nonempty) (H : BddAbove s) : IsLUB s (supₛ s) :=
  ⟨fun x => le_csupₛ H, fun x => csupₛ_le Ne⟩
#align is_lub_cSup isLUB_csupₛ

/- warning: is_lub_csupr -> isLUB_csupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align is_lub_csupr isLUB_csupᵢₓ'. -/
theorem isLUB_csupᵢ [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csupₛ (range_nonempty f) H
#align is_lub_csupr isLUB_csupᵢ

/- warning: is_lub_csupr_set -> isLUB_csupᵢ_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (Set.Nonempty.{u2} β s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (Set.Nonempty.{u2} β s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))))
Case conversion may be inaccurate. Consider using '#align is_lub_csupr_set isLUB_csupᵢ_setₓ'. -/
theorem isLUB_csupᵢ_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← supₛ_image']
  exact isLUB_csupₛ (Hne.image _) H
#align is_lub_csupr_set isLUB_csupᵢ_set

/- warning: is_glb_cInf -> isGLB_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align is_glb_cInf isGLB_cinfₛₓ'. -/
theorem isGLB_cinfₛ (ne : s.Nonempty) (H : BddBelow s) : IsGLB s (infₛ s) :=
  ⟨fun x => cinfₛ_le H, fun x => le_cinfₛ Ne⟩
#align is_glb_cInf isGLB_cinfₛ

/- warning: is_glb_cinfi -> isGLB_cinfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align is_glb_cinfi isGLB_cinfᵢₓ'. -/
theorem isGLB_cinfᵢ [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_cinfₛ (range_nonempty f) H
#align is_glb_cinfi isGLB_cinfᵢ

/- warning: is_glb_cinfi_set -> isGLB_cinfᵢ_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (Set.Nonempty.{u2} β s) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (Set.Nonempty.{u2} β s) -> (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))))
Case conversion may be inaccurate. Consider using '#align is_glb_cinfi_set isGLB_cinfᵢ_setₓ'. -/
theorem isGLB_cinfᵢ_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  @isLUB_csupᵢ_set αᵒᵈ _ _ _ _ H Hne
#align is_glb_cinfi_set isGLB_cinfᵢ_set

/- warning: csupr_le_iff -> csupᵢ_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f) a) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι f) a) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align csupr_le_iff csupᵢ_le_iffₓ'. -/
theorem csupᵢ_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    supᵢ f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_csupᵢ hf).trans forall_range_iff
#align csupr_le_iff csupᵢ_le_iff

/- warning: le_cinfi_iff -> le_cinfᵢ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f i)))
Case conversion may be inaccurate. Consider using '#align le_cinfi_iff le_cinfᵢ_iffₓ'. -/
theorem le_cinfᵢ_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ infᵢ f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| isGLB_cinfᵢ hf).trans forall_range_iff
#align le_cinfi_iff le_cinfᵢ_iff

/- warning: csupr_set_le_iff -> csupᵢ_set_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> α} {a : α}, (Set.Nonempty.{u2} ι s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} ι α f s)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i))) a) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> α} {a : α}, (Set.Nonempty.{u2} ι s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} ι α f s)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i))) a) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) a)))
Case conversion may be inaccurate. Consider using '#align csupr_set_le_iff csupᵢ_set_le_iffₓ'. -/
theorem csupᵢ_set_le_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : (⨆ i : s, f i) ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_csupᵢ_set hf hs).trans ball_image_iff
#align csupr_set_le_iff csupᵢ_set_le_iff

/- warning: le_cinfi_set_iff -> le_cinfᵢ_set_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> α} {a : α}, (Set.Nonempty.{u2} ι s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} ι α f s)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i)))) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> α} {a : α}, (Set.Nonempty.{u2} ι s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} ι α f s)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i)))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f i))))
Case conversion may be inaccurate. Consider using '#align le_cinfi_set_iff le_cinfᵢ_set_iffₓ'. -/
theorem le_cinfᵢ_set_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| isGLB_cinfᵢ_set hf hs).trans ball_image_iff
#align le_cinfi_set_iff le_cinfᵢ_set_iff

/- warning: is_lub.cSup_eq -> IsLUB.csupₛ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_lub.cSup_eq IsLUB.csupₛ_eqₓ'. -/
theorem IsLUB.csupₛ_eq (H : IsLUB s a) (ne : s.Nonempty) : supₛ s = a :=
  (isLUB_csupₛ Ne ⟨a, H.1⟩).unique H
#align is_lub.cSup_eq IsLUB.csupₛ_eq

/- warning: is_lub.csupr_eq -> IsLUB.csupᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i)) a)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => f i)) a)
Case conversion may be inaccurate. Consider using '#align is_lub.csupr_eq IsLUB.csupᵢ_eqₓ'. -/
theorem IsLUB.csupᵢ_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : (⨆ i, f i) = a :=
  H.csupₛ_eq (range_nonempty f)
#align is_lub.csupr_eq IsLUB.csupᵢ_eq

/- warning: is_lub.csupr_set_eq -> IsLUB.csupᵢ_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {s : Set.{u2} β} {f : β -> α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) a) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {s : Set.{u2} β} {f : β -> α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) a) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))) a)
Case conversion may be inaccurate. Consider using '#align is_lub.csupr_set_eq IsLUB.csupᵢ_set_eqₓ'. -/
theorem IsLUB.csupᵢ_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    (⨆ i : s, f i) = a :=
  IsLUB.csupₛ_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_lub.csupr_set_eq IsLUB.csupᵢ_set_eq

/- warning: is_greatest.cSup_eq -> IsGreatest.csupₛ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGreatest.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGreatest.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_greatest.cSup_eq IsGreatest.csupₛ_eqₓ'. -/
/-- A greatest element of a set is the supremum of this set. -/
theorem IsGreatest.csupₛ_eq (H : IsGreatest s a) : supₛ s = a :=
  H.IsLUB.csupₛ_eq H.Nonempty
#align is_greatest.cSup_eq IsGreatest.csupₛ_eq

/- warning: is_greatest.Sup_mem -> IsGreatest.csupₛ_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGreatest.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGreatest.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) s)
Case conversion may be inaccurate. Consider using '#align is_greatest.Sup_mem IsGreatest.csupₛ_memₓ'. -/
theorem IsGreatest.csupₛ_mem (H : IsGreatest s a) : supₛ s ∈ s :=
  H.csupₛ_eq.symm ▸ H.1
#align is_greatest.Sup_mem IsGreatest.csupₛ_mem

/- warning: is_glb.cInf_eq -> IsGLB.cinfₛ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_glb.cInf_eq IsGLB.cinfₛ_eqₓ'. -/
theorem IsGLB.cinfₛ_eq (H : IsGLB s a) (ne : s.Nonempty) : infₛ s = a :=
  (isGLB_cinfₛ Ne ⟨a, H.1⟩).unique H
#align is_glb.cInf_eq IsGLB.cinfₛ_eq

/- warning: is_glb.cinfi_eq -> IsGLB.cinfᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => f i)) a)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => f i)) a)
Case conversion may be inaccurate. Consider using '#align is_glb.cinfi_eq IsGLB.cinfᵢ_eqₓ'. -/
theorem IsGLB.cinfᵢ_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : (⨅ i, f i) = a :=
  H.cinfₛ_eq (range_nonempty f)
#align is_glb.cinfi_eq IsGLB.cinfᵢ_eq

/- warning: is_glb.cinfi_set_eq -> IsGLB.cinfᵢ_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {s : Set.{u2} β} {f : β -> α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) a) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {s : Set.{u2} β} {f : β -> α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s) a) -> (Set.Nonempty.{u2} β s) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))) a)
Case conversion may be inaccurate. Consider using '#align is_glb.cinfi_set_eq IsGLB.cinfᵢ_set_eqₓ'. -/
theorem IsGLB.cinfᵢ_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    (⨅ i : s, f i) = a :=
  IsGLB.cinfₛ_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_glb.cinfi_set_eq IsGLB.cinfᵢ_set_eq

/- warning: is_least.cInf_eq -> IsLeast.cinfₛ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_least.cInf_eq IsLeast.cinfₛ_eqₓ'. -/
/-- A least element of a set is the infimum of this set. -/
theorem IsLeast.cinfₛ_eq (H : IsLeast s a) : infₛ s = a :=
  H.IsGLB.cinfₛ_eq H.Nonempty
#align is_least.cInf_eq IsLeast.cinfₛ_eq

/- warning: is_least.Inf_mem -> IsLeast.cinfₛ_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s a) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) s)
Case conversion may be inaccurate. Consider using '#align is_least.Inf_mem IsLeast.cinfₛ_memₓ'. -/
theorem IsLeast.cinfₛ_mem (H : IsLeast s a) : infₛ s ∈ s :=
  H.cinfₛ_eq.symm ▸ H.1
#align is_least.Inf_mem IsLeast.cinfₛ_mem

/- warning: subset_Icc_cInf_cSup -> subset_Icc_cinfₛ_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align subset_Icc_cInf_cSup subset_Icc_cinfₛ_csupₛₓ'. -/
theorem subset_Icc_cinfₛ_csupₛ (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (infₛ s) (supₛ s) :=
  fun x hx => ⟨cinfₛ_le hb hx, le_csupₛ ha hx⟩
#align subset_Icc_cInf_cSup subset_Icc_cinfₛ_csupₛ

/- warning: cSup_le_iff -> csupₛ_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)))
Case conversion may be inaccurate. Consider using '#align cSup_le_iff csupₛ_le_iffₓ'. -/
theorem csupₛ_le_iff (hb : BddAbove s) (hs : s.Nonempty) : supₛ s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csupₛ hs hb)
#align cSup_le_iff csupₛ_le_iff

/- warning: le_cInf_iff -> le_cinfₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_cInf_iff le_cinfₛ_iffₓ'. -/
theorem le_cinfₛ_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ infₛ s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_cinfₛ hs hb)
#align le_cInf_iff le_cinfₛ_iff

/- warning: cSup_lower_bounds_eq_cInf -> csupₛ_lower_bounds_eq_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align cSup_lower_bounds_eq_cInf csupₛ_lower_bounds_eq_cinfₛₓ'. -/
theorem csupₛ_lower_bounds_eq_cinfₛ {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    supₛ (lowerBounds s) = infₛ s :=
  (isLUB_csupₛ h <| hs.mono fun x hx y hy => hy hx).unique (isGLB_cinfₛ hs h).IsLUB
#align cSup_lower_bounds_eq_cInf csupₛ_lower_bounds_eq_cinfₛ

/- warning: cInf_upper_bounds_eq_cSup -> cinfₛ_upper_bounds_eq_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s)) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align cInf_upper_bounds_eq_cSup cinfₛ_upper_bounds_eq_csupₛₓ'. -/
theorem cinfₛ_upper_bounds_eq_csupₛ {s : Set α} (h : BddAbove s) (hs : s.Nonempty) :
    infₛ (upperBounds s) = supₛ s :=
  (isGLB_cinfₛ h <| hs.mono fun x hx y hy => hy hx).unique (isLUB_csupₛ hs h).IsGLB
#align cInf_upper_bounds_eq_cSup cinfₛ_upper_bounds_eq_csupₛ

/- warning: not_mem_of_lt_cInf -> not_mem_of_lt_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {x : α} {s : Set.{u1} α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) x (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {x : α} {s : Set.{u1} α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) x (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s)) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))
Case conversion may be inaccurate. Consider using '#align not_mem_of_lt_cInf not_mem_of_lt_cinfₛₓ'. -/
theorem not_mem_of_lt_cinfₛ {x : α} {s : Set α} (h : x < infₛ s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (cinfₛ_le hs hx))
#align not_mem_of_lt_cInf not_mem_of_lt_cinfₛ

/- warning: not_mem_of_cSup_lt -> not_mem_of_csupₛ_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {x : α} {s : Set.{u1} α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) x) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {x : α} {s : Set.{u1} α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) x) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))
Case conversion may be inaccurate. Consider using '#align not_mem_of_cSup_lt not_mem_of_csupₛ_ltₓ'. -/
theorem not_mem_of_csupₛ_lt {x : α} {s : Set α} (h : supₛ s < x) (hs : BddAbove s) : x ∉ s :=
  @not_mem_of_lt_cinfₛ αᵒᵈ _ x s h hs
#align not_mem_of_cSup_lt not_mem_of_csupₛ_lt

/- warning: cSup_eq_of_forall_le_of_forall_lt_exists_gt -> csupₛ_eq_of_forall_le_of_forall_lt_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w b) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w a)))) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w b) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w a)))) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align cSup_eq_of_forall_le_of_forall_lt_exists_gt csupₛ_eq_of_forall_le_of_forall_lt_exists_gtₓ'. -/
/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `Sup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csupₛ_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : supₛ s = b :=
  eq_of_le_of_not_lt (csupₛ_le hs H) fun hb =>
    let ⟨a, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_csupₛ ⟨b, H⟩ ha
#align cSup_eq_of_forall_le_of_forall_lt_exists_gt csupₛ_eq_of_forall_le_of_forall_lt_exists_gt

/- warning: cInf_eq_of_forall_ge_of_forall_gt_exists_lt -> cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b w) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a w)))) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b w) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a w)))) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align cInf_eq_of_forall_ge_of_forall_gt_exists_lt cinfₛ_eq_of_forall_ge_of_forall_gt_exists_ltₓ'. -/
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `Inf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → infₛ s = b :=
  @csupₛ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align cInf_eq_of_forall_ge_of_forall_gt_exists_lt cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt

/- warning: lt_cSup_of_lt -> lt_csupₛ_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align lt_cSup_of_lt lt_csupₛ_of_ltₓ'. -/
/-- b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem lt_csupₛ_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < supₛ s :=
  lt_of_lt_of_le h (le_csupₛ hs ha)
#align lt_cSup_of_lt lt_csupₛ_of_lt

/- warning: cInf_lt_of_lt -> cinfₛ_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align cInf_lt_of_lt cinfₛ_lt_of_ltₓ'. -/
/-- Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem cinfₛ_lt_of_lt : BddBelow s → a ∈ s → a < b → infₛ s < b :=
  @lt_csupₛ_of_lt αᵒᵈ _ _ _ _
#align cInf_lt_of_lt cinfₛ_lt_of_lt

/- warning: exists_between_of_forall_le -> exists_between_of_forall_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α t) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) x y))) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α t) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) x y))) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t)))
Case conversion may be inaccurate. Consider using '#align exists_between_of_forall_le exists_between_of_forall_leₓ'. -/
/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨infₛ t, fun x hx => le_cinfₛ tne <| hst x hx, fun y hy => cinfₛ_le (sne.mono hst) hy⟩
#align exists_between_of_forall_le exists_between_of_forall_le

/- warning: cSup_singleton -> csupₛ_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) a
Case conversion may be inaccurate. Consider using '#align cSup_singleton csupₛ_singletonₓ'. -/
/-- The supremum of a singleton is the element of the singleton-/
@[simp]
theorem csupₛ_singleton (a : α) : supₛ {a} = a :=
  isGreatest_singleton.csupₛ_eq
#align cSup_singleton csupₛ_singleton

/- warning: cInf_singleton -> cinfₛ_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) a
Case conversion may be inaccurate. Consider using '#align cInf_singleton cinfₛ_singletonₓ'. -/
/-- The infimum of a singleton is the element of the singleton-/
@[simp]
theorem cinfₛ_singleton (a : α) : infₛ {a} = a :=
  isLeast_singleton.cinfₛ_eq
#align cInf_singleton cinfₛ_singleton

/- warning: cSup_pair -> csupₛ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α) (b : α), Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align cSup_pair csupₛ_pairₓ'. -/
@[simp]
theorem csupₛ_pair (a b : α) : supₛ {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csupₛ_eq (insert_nonempty _ _)
#align cSup_pair csupₛ_pair

/- warning: cInf_pair -> cinfₛ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α) (b : α), Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] (a : α) (b : α), Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align cInf_pair cinfₛ_pairₓ'. -/
@[simp]
theorem cinfₛ_pair (a b : α) : infₛ {a, b} = a ⊓ b :=
  (@isGLB_pair _ _ a b).cinfₛ_eq (insert_nonempty _ _)
#align cInf_pair cinfₛ_pair

/- warning: cInf_le_cSup -> cinfₛ_le_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align cInf_le_cSup cinfₛ_le_csupₛₓ'. -/
/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cinfₛ_le_csupₛ (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) : infₛ s ≤ supₛ s :=
  isGLB_le_isLUB (isGLB_cinfₛ Ne hb) (isLUB_csupₛ Ne ha) Ne
#align cInf_le_cSup cinfₛ_le_csupₛ

/- warning: cSup_union -> csupₛ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) t)))
Case conversion may be inaccurate. Consider using '#align cSup_union csupₛ_unionₓ'. -/
/-- The sup of a union of two sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem csupₛ_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    supₛ (s ∪ t) = supₛ s ⊔ supₛ t :=
  ((isLUB_csupₛ sne hs).union (isLUB_csupₛ tne ht)).csupₛ_eq sne.inl
#align cSup_union csupₛ_union

/- warning: cInf_union -> cinfₛ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) t)))
Case conversion may be inaccurate. Consider using '#align cInf_union cinfₛ_unionₓ'. -/
/-- The inf of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cinfₛ_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    infₛ (s ∪ t) = infₛ s ⊓ infₛ t :=
  @csupₛ_union αᵒᵈ _ _ _ hs sne ht tne
#align cInf_union cinfₛ_union

/- warning: cSup_inter_le -> csupₛ_inter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) t)))
Case conversion may be inaccurate. Consider using '#align cSup_inter_le csupₛ_inter_leₓ'. -/
/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem csupₛ_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    supₛ (s ∩ t) ≤ supₛ s ⊓ supₛ t :=
  csupₛ_le hst fun x hx => le_inf (le_csupₛ hs hx.1) (le_csupₛ ht hx.2)
#align cSup_inter_le csupₛ_inter_le

/- warning: le_cInf_inter -> le_cinfₛ_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) t)) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) t) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) t)) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align le_cInf_inter le_cinfₛ_interₓ'. -/
/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cinfₛ_inter :
    BddBelow s → BddBelow t → (s ∩ t).Nonempty → infₛ s ⊔ infₛ t ≤ infₛ (s ∩ t) :=
  @csupₛ_inter_le αᵒᵈ _ _ _
#align le_cInf_inter le_cinfₛ_inter

/- warning: cSup_insert -> csupₛ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align cSup_insert csupₛ_insertₓ'. -/
/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem csupₛ_insert (hs : BddAbove s) (sne : s.Nonempty) : supₛ (insert a s) = a ⊔ supₛ s :=
  ((isLUB_csupₛ sne hs).insert a).csupₛ_eq (insert_nonempty a s)
#align cSup_insert csupₛ_insert

/- warning: cInf_insert -> cinfₛ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {a : α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align cInf_insert cinfₛ_insertₓ'. -/
/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cinfₛ_insert (hs : BddBelow s) (sne : s.Nonempty) : infₛ (insert a s) = a ⊓ infₛ s :=
  @csupₛ_insert αᵒᵈ _ _ _ hs sne
#align cInf_insert cinfₛ_insert

/- warning: cInf_Icc -> cinfₛ_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
Case conversion may be inaccurate. Consider using '#align cInf_Icc cinfₛ_Iccₓ'. -/
@[simp]
theorem cinfₛ_Icc (h : a ≤ b) : infₛ (Icc a b) = a :=
  (isGLB_Icc h).cinfₛ_eq (nonempty_Icc.2 h)
#align cInf_Icc cinfₛ_Icc

/- warning: cInf_Ici -> cinfₛ_Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
Case conversion may be inaccurate. Consider using '#align cInf_Ici cinfₛ_Iciₓ'. -/
@[simp]
theorem cinfₛ_Ici : infₛ (Ici a) = a :=
  isLeast_Ici.cinfₛ_eq
#align cInf_Ici cinfₛ_Ici

/- warning: cInf_Ico -> cinfₛ_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
Case conversion may be inaccurate. Consider using '#align cInf_Ico cinfₛ_Icoₓ'. -/
@[simp]
theorem cinfₛ_Ico (h : a < b) : infₛ (Ico a b) = a :=
  (isGLB_Ico h).cinfₛ_eq (nonempty_Ico.2 h)
#align cInf_Ico cinfₛ_Ico

/- warning: cInf_Ioc -> cinfₛ_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
Case conversion may be inaccurate. Consider using '#align cInf_Ioc cinfₛ_Iocₓ'. -/
@[simp]
theorem cinfₛ_Ioc [DenselyOrdered α] (h : a < b) : infₛ (Ioc a b) = a :=
  (isGLB_Ioc h).cinfₛ_eq (nonempty_Ioc.2 h)
#align cInf_Ioc cinfₛ_Ioc

/- warning: cInf_Ioi -> cinfₛ_Ioi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
Case conversion may be inaccurate. Consider using '#align cInf_Ioi cinfₛ_Ioiₓ'. -/
@[simp]
theorem cinfₛ_Ioi [NoMaxOrder α] [DenselyOrdered α] : infₛ (Ioi a) = a :=
  cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_lt) fun w hw => by
    simpa using exists_between hw
#align cInf_Ioi cinfₛ_Ioi

/- warning: cInf_Ioo -> cinfₛ_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) a)
Case conversion may be inaccurate. Consider using '#align cInf_Ioo cinfₛ_Iooₓ'. -/
@[simp]
theorem cinfₛ_Ioo [DenselyOrdered α] (h : a < b) : infₛ (Ioo a b) = a :=
  (isGLB_Ioo h).cinfₛ_eq (nonempty_Ioo.2 h)
#align cInf_Ioo cinfₛ_Ioo

/- warning: cSup_Icc -> csupₛ_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
Case conversion may be inaccurate. Consider using '#align cSup_Icc csupₛ_Iccₓ'. -/
@[simp]
theorem csupₛ_Icc (h : a ≤ b) : supₛ (Icc a b) = b :=
  (isLUB_Icc h).csupₛ_eq (nonempty_Icc.2 h)
#align cSup_Icc csupₛ_Icc

/- warning: cSup_Ico -> csupₛ_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
Case conversion may be inaccurate. Consider using '#align cSup_Ico csupₛ_Icoₓ'. -/
@[simp]
theorem csupₛ_Ico [DenselyOrdered α] (h : a < b) : supₛ (Ico a b) = b :=
  (isLUB_Ico h).csupₛ_eq (nonempty_Ico.2 h)
#align cSup_Ico csupₛ_Ico

/- warning: cSup_Iic -> csupₛ_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
Case conversion may be inaccurate. Consider using '#align cSup_Iic csupₛ_Iicₓ'. -/
@[simp]
theorem csupₛ_Iic : supₛ (Iic a) = a :=
  isGreatest_Iic.csupₛ_eq
#align cSup_Iic csupₛ_Iic

/- warning: cSup_Iio -> csupₛ_Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} [_inst_2 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Iio.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a)) a
Case conversion may be inaccurate. Consider using '#align cSup_Iio csupₛ_Iioₓ'. -/
@[simp]
theorem csupₛ_Iio [NoMinOrder α] [DenselyOrdered α] : supₛ (Iio a) = a :=
  csupₛ_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm'] using exists_between hw
#align cSup_Iio csupₛ_Iio

/- warning: cSup_Ioc -> csupₛ_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
Case conversion may be inaccurate. Consider using '#align cSup_Ioc csupₛ_Iocₓ'. -/
@[simp]
theorem csupₛ_Ioc (h : a < b) : supₛ (Ioc a b) = b :=
  (isLUB_Ioc h).csupₛ_eq (nonempty_Ioc.2 h)
#align cSup_Ioc csupₛ_Ioc

/- warning: cSup_Ioo -> csupₛ_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {b : α} [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))], (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) a b)) b)
Case conversion may be inaccurate. Consider using '#align cSup_Ioo csupₛ_Iooₓ'. -/
@[simp]
theorem csupₛ_Ioo [DenselyOrdered α] (h : a < b) : supₛ (Ioo a b) = b :=
  (isLUB_Ioo h).csupₛ_eq (nonempty_Ioo.2 h)
#align cSup_Ioo csupₛ_Ioo

/- warning: csupr_le -> csupᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {c : α}, (forall (x : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f x) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f) c)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {c : α}, (forall (x : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f x) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι f) c)
Case conversion may be inaccurate. Consider using '#align csupr_le csupᵢ_leₓ'. -/
/-- The indexed supremum of a function is bounded above by a uniform bound-/
theorem csupᵢ_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : supᵢ f ≤ c :=
  csupₛ_le (range_nonempty f) (by rwa [forall_range_iff])
#align csupr_le csupᵢ_le

/- warning: le_csupr -> le_csupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (c : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f c) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : ι -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (c : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (f c) (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align le_csupr le_csupᵢₓ'. -/
/-- The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_csupᵢ {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ supᵢ f :=
  le_csupₛ H (mem_range_self _)
#align le_csupr le_csupᵢ

/- warning: le_csupr_of_le -> le_csupᵢ_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (c : ι), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (f c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {a : α} {f : ι -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (c : ι), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) a (f c)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) a (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) ι f)))
Case conversion may be inaccurate. Consider using '#align le_csupr_of_le le_csupᵢ_of_leₓ'. -/
theorem le_csupᵢ_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ supᵢ f :=
  le_trans h (le_csupᵢ H c)
#align le_csupr_of_le le_csupᵢ_of_le

/- warning: csupr_mono -> csupᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι g)) -> (forall (x : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f x) (g x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι f) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι g)) -> (forall (x : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (f x) (g x)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) ι f) (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) ι g))
Case conversion may be inaccurate. Consider using '#align csupr_mono csupᵢ_monoₓ'. -/
/-- The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem csupᵢ_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) : supᵢ f ≤ supᵢ g :=
  by
  cases isEmpty_or_nonempty ι
  · rw [supᵢ_of_empty', supᵢ_of_empty']
  · exact csupᵢ_le fun x => le_csupᵢ_of_le B x (H x)
#align csupr_mono csupᵢ_mono

/- warning: le_csupr_set -> le_csupᵢ_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (forall {c : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f c) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (forall {c : β}, (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f c) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i)))))
Case conversion may be inaccurate. Consider using '#align le_csupr_set le_csupᵢ_setₓ'. -/
theorem le_csupᵢ_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_csupₛ H <| mem_image_of_mem f hc).trans_eq supₛ_image'
#align le_csupr_set le_csupᵢ_set

/- warning: cinfi_mono -> cinfᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (x : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f x) (g x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (x : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (f x) (g x)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (infᵢ.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) ι f) (infᵢ.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) ι g))
Case conversion may be inaccurate. Consider using '#align cinfi_mono cinfᵢ_monoₓ'. -/
/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem cinfᵢ_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : infᵢ f ≤ infᵢ g :=
  @csupᵢ_mono αᵒᵈ _ _ _ _ B H
#align cinfi_mono cinfᵢ_mono

/- warning: le_cinfi -> le_cinfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {c : α}, (forall (x : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) c (f x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) c (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {c : α}, (forall (x : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) c (f x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) c (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align le_cinfi le_cinfᵢₓ'. -/
/-- The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_cinfᵢ [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ infᵢ f :=
  @csupᵢ_le αᵒᵈ _ _ _ _ _ H
#align le_cinfi le_cinfᵢ

/- warning: cinfi_le -> cinfᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (c : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f) (f c))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : ι -> α}, (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (c : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (infᵢ.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) ι f) (f c))
Case conversion may be inaccurate. Consider using '#align cinfi_le cinfᵢ_leₓ'. -/
/-- The indexed infimum of a function is bounded above by the value taken at one point-/
theorem cinfᵢ_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : infᵢ f ≤ f c :=
  @le_csupᵢ αᵒᵈ _ _ _ H c
#align cinfi_le cinfᵢ_le

/- warning: cinfi_le_of_le -> cinfᵢ_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {a : α} {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u2} α ι f)) -> (forall (c : ι), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f c) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι f) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {a : α} {f : ι -> α}, (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (Set.range.{u2, u1} α ι f)) -> (forall (c : ι), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (f c) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (infᵢ.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) ι f) a))
Case conversion may be inaccurate. Consider using '#align cinfi_le_of_le cinfᵢ_le_of_leₓ'. -/
theorem cinfᵢ_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : infᵢ f ≤ a :=
  @le_csupᵢ_of_le αᵒᵈ _ _ _ _ H c h
#align cinfi_le_of_le cinfᵢ_le_of_le

/- warning: cinfi_set_le -> cinfᵢ_set_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (forall {c : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) i))) (f c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u2, u1} β α f s)) -> (forall {c : β}, (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} β s) (fun (i : Set.Elem.{u2} β s) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) i))) (f c)))
Case conversion may be inaccurate. Consider using '#align cinfi_set_le cinfᵢ_set_leₓ'. -/
theorem cinfᵢ_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    (⨅ i : s, f i) ≤ f c :=
  @le_csupᵢ_set αᵒᵈ _ _ _ _ H _ hc
#align cinfi_set_le cinfᵢ_set_le

/- warning: csupr_const -> csupᵢ_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [hι : Nonempty.{u2} ι] {a : α}, Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (b : ι) => a)) a
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [hι : Nonempty.{u2} ι] {a : α}, Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (b : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align csupr_const csupᵢ_constₓ'. -/
@[simp]
theorem csupᵢ_const [hι : Nonempty ι] {a : α} : (⨆ b : ι, a) = a := by
  rw [supᵢ, range_const, csupₛ_singleton]
#align csupr_const csupᵢ_const

/- warning: cinfi_const -> cinfᵢ_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [hι : Nonempty.{u2} ι] {a : α}, Eq.{succ u1} α (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (b : ι) => a)) a
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [hι : Nonempty.{u2} ι] {a : α}, Eq.{succ u1} α (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (b : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align cinfi_const cinfᵢ_constₓ'. -/
@[simp]
theorem cinfᵢ_const [hι : Nonempty ι] {a : α} : (⨅ b : ι, a) = a :=
  @csupᵢ_const αᵒᵈ _ _ _ _
#align cinfi_const cinfᵢ_const

/- warning: supr_unique -> csupᵢ_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Unique.{u2} ι] {s : ι -> α}, Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => s i)) (s (Inhabited.default.{u2} ι (Unique.inhabited.{u2} ι _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Unique.{u2} ι] {s : ι -> α}, Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => s i)) (s (Inhabited.default.{u2} ι (Unique.instInhabited.{u2} ι _inst_2)))
Case conversion may be inaccurate. Consider using '#align supr_unique csupᵢ_uniqueₓ'. -/
@[simp]
theorem csupᵢ_unique [Unique ι] {s : ι → α} : (⨆ i, s i) = s default :=
  by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, csupᵢ_const]
#align supr_unique csupᵢ_unique

/- warning: infi_unique -> cinfᵢ_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Unique.{u2} ι] {s : ι -> α}, Eq.{succ u1} α (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => s i)) (s (Inhabited.default.{u2} ι (Unique.inhabited.{u2} ι _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : Unique.{u2} ι] {s : ι -> α}, Eq.{succ u1} α (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => s i)) (s (Inhabited.default.{u2} ι (Unique.instInhabited.{u2} ι _inst_2)))
Case conversion may be inaccurate. Consider using '#align infi_unique cinfᵢ_uniqueₓ'. -/
@[simp]
theorem cinfᵢ_unique [Unique ι] {s : ι → α} : (⨅ i, s i) = s default :=
  @csupᵢ_unique αᵒᵈ _ _ _ _
#align infi_unique cinfᵢ_unique

/- warning: csupr_pos -> csupᵢ_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (supᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (supᵢ.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
Case conversion may be inaccurate. Consider using '#align csupr_pos csupᵢ_posₓ'. -/
@[simp]
theorem csupᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  haveI := uniqueProp hp
  csupᵢ_unique
#align csupr_pos csupᵢ_pos

/- warning: cinfi_pos -> cinfᵢ_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (infᵢ.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
Case conversion may be inaccurate. Consider using '#align cinfi_pos cinfᵢ_posₓ'. -/
@[simp]
theorem cinfᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  @csupᵢ_pos αᵒᵈ _ _ _ hp
#align cinfi_pos cinfᵢ_pos

/- warning: csupr_eq_of_forall_le_of_forall_lt_exists_gt -> csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) b) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w b) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w (f i)))) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i)) b)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) b) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w b) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) w (f i)))) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => f i)) b)
Case conversion may be inaccurate. Consider using '#align csupr_eq_of_forall_le_of_forall_lt_exists_gt csupᵢ_eq_of_forall_le_of_forall_lt_exists_gtₓ'. -/
/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `supr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  csupₛ_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_range_iff.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw
#align csupr_eq_of_forall_le_of_forall_lt_exists_gt csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt

/- warning: cinfi_eq_of_forall_ge_of_forall_gt_exists_lt -> cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b (f i)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b w) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) w))) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => f i)) b)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b (f i)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b w) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f i) w))) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => f i)) b)
Case conversion may be inaccurate. Consider using '#align cinfi_eq_of_forall_ge_of_forall_gt_exists_lt cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_ltₓ'. -/
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `infi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : (⨅ i : ι, f i) = b :=
  @csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _ ‹_› ‹_› ‹_›
#align cinfi_eq_of_forall_ge_of_forall_gt_exists_lt cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt

/- warning: monotone.csupr_mem_Inter_Icc_of_antitone -> Monotone.csupᵢ_mem_Inter_Icc_of_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : β -> α} {g : β -> α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) f) -> (Antitone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) g) -> (LE.le.{max u2 u1} (β -> α) (Pi.hasLe.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) f g) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) β (fun (n : β) => f n)) (Set.interᵢ.{u1, succ u2} α β (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : β -> α} {g : β -> α}, (Monotone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) f) -> (Antitone.{u2, u1} β α (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) g) -> (LE.le.{max u1 u2} (β -> α) (Pi.hasLe.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) f g) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) β (fun (n : β) => f n)) (Set.interᵢ.{u1, succ u2} α β (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))))
Case conversion may be inaccurate. Consider using '#align monotone.csupr_mem_Inter_Icc_of_antitone Monotone.csupᵢ_mem_Inter_Icc_of_antitoneₓ'. -/
/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.csupᵢ_mem_Inter_Icc_of_antitone [SemilatticeSup β] {f g : β → α} (hf : Monotone f)
    (hg : Antitone g) (h : f ≤ g) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  by
  refine' mem_Inter.2 fun n => _
  haveI : Nonempty β := ⟨n⟩
  have : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  exact ⟨le_csupᵢ ⟨g <| n, forall_range_iff.2 this⟩ _, csupᵢ_le this⟩
#align monotone.csupr_mem_Inter_Icc_of_antitone Monotone.csupᵢ_mem_Inter_Icc_of_antitone

/- warning: csupr_mem_Inter_Icc_of_antitone_Icc -> csupᵢ_mem_Inter_Icc_of_antitone_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : β -> α} {g : β -> α}, (Antitone.{u2, u1} β (Set.{u1} α) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))) -> (forall (n : β), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f n) (g n)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) β (fun (n : β) => f n)) (Set.interᵢ.{u1, succ u2} α β (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : β -> α} {g : β -> α}, (Antitone.{u2, u1} β (Set.{u1} α) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))) -> (forall (n : β), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (f n) (g n)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (supᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) β (fun (n : β) => f n)) (Set.interᵢ.{u1, succ u2} α β (fun (n : β) => Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (f n) (g n))))
Case conversion may be inaccurate. Consider using '#align csupr_mem_Inter_Icc_of_antitone_Icc csupᵢ_mem_Inter_Icc_of_antitone_Iccₓ'. -/
/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem csupᵢ_mem_Inter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.csupᵢ_mem_Inter_Icc_of_antitone
    (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'
#align csupr_mem_Inter_Icc_of_antitone_Icc csupᵢ_mem_Inter_Icc_of_antitone_Icc

/- warning: cSup_eq_of_is_forall_le_of_forall_le_imp_ge -> csupₛ_eq_of_is_forall_le_of_forall_le_imp_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (forall (ub : α), (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a ub)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b ub)) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a b)) -> (forall (ub : α), (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a ub)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) b ub)) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align cSup_eq_of_is_forall_le_of_forall_le_imp_ge csupₛ_eq_of_is_forall_le_of_forall_le_imp_geₓ'. -/
/-- Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem csupₛ_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : supₛ s = b :=
  (csupₛ_le hs h_is_ub).antisymm (h_b_le_ub _ fun a => le_csupₛ ⟨b, h_is_ub⟩)
#align cSup_eq_of_is_forall_le_of_forall_le_imp_ge csupₛ_eq_of_is_forall_le_of_forall_le_imp_ge

end ConditionallyCompleteLattice

#print Pi.conditionallyCompleteLattice /-
instance Pi.conditionallyCompleteLattice {ι : Type _} {α : ∀ i : ι, Type _}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) :=
  { Pi.lattice, Pi.supSet,
    Pi.infSet with
    le_cSup := fun s f ⟨g, hg⟩ hf i =>
      le_csupₛ ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    cSup_le := fun s f hs hf i =>
      csupₛ_le (by haveI := hs.to_subtype <;> apply range_nonempty) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i
    cInf_le := fun s f ⟨g, hg⟩ hf i =>
      cinfₛ_le ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    le_cInf := fun s f hs hf i =>
      le_cinfₛ (by haveI := hs.to_subtype <;> apply range_nonempty) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i }
#align pi.conditionally_complete_lattice Pi.conditionallyCompleteLattice
-/

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/- warning: exists_lt_of_lt_cSup -> exists_lt_of_lt_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b a)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_lt_cSup exists_lt_of_lt_csupₛₓ'. -/
/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
theorem exists_lt_of_lt_csupₛ (hs : s.Nonempty) (hb : b < supₛ s) : ∃ a ∈ s, b < a :=
  by
  contrapose! hb
  exact csupₛ_le hs hb
#align exists_lt_of_lt_cSup exists_lt_of_lt_csupₛ

/- warning: exists_lt_of_lt_csupr -> exists_lt_of_lt_csupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f)) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {b : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f)) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (f i)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_lt_csupr exists_lt_of_lt_csupᵢₓ'. -/
/-- Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_csupᵢ [Nonempty ι] {f : ι → α} (h : b < supᵢ f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csupₛ (range_nonempty f) h
  ⟨i, h⟩
#align exists_lt_of_lt_csupr exists_lt_of_lt_csupᵢ

/- warning: exists_lt_of_cInf_lt -> exists_lt_of_cinfₛ_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) b) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, (Set.Nonempty.{u1} α s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) b) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) a b)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_cInf_lt exists_lt_of_cinfₛ_ltₓ'. -/
/-- When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
theorem exists_lt_of_cinfₛ_lt (hs : s.Nonempty) (hb : infₛ s < b) : ∃ a ∈ s, a < b :=
  @exists_lt_of_lt_csupₛ αᵒᵈ _ _ _ hs hb
#align exists_lt_of_cInf_lt exists_lt_of_cinfₛ_lt

/- warning: exists_lt_of_cinfi_lt -> exists_lt_of_cinfᵢ_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f) a) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι] {f : ι -> α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f) a) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_cinfi_lt exists_lt_of_cinfᵢ_ltₓ'. -/
/-- Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_cinfᵢ_lt [Nonempty ι] {f : ι → α} (h : infᵢ f < a) : ∃ i, f i < a :=
  @exists_lt_of_lt_csupᵢ αᵒᵈ _ _ _ _ _ h
#align exists_lt_of_cinfi_lt exists_lt_of_cinfᵢ_lt

open Function

variable [IsWellOrder α (· < ·)]

/- warning: Inf_eq_argmin_on -> infₛ_eq_argmin_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))] (hs : Set.Nonempty.{u1} α s), Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) (Function.argminOn.{u1, u1} α α (id.{succ u1} α) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (IsWellFounded.wf.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))))) (IsWellOrder.to_isWellFounded.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))))) _inst_2)) s hs)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8927 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8929 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8927 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8929)] (hs : Set.Nonempty.{u1} α s), Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) (Function.argminOn.{u1, u1} α α (id.{succ u1} α) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (IsWellFounded.wf.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8954 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8956 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8954 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8956) (IsWellOrder.toIsWellFounded.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8954 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8956 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8954 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.8956) _inst_2)) s hs)
Case conversion may be inaccurate. Consider using '#align Inf_eq_argmin_on infₛ_eq_argmin_onₓ'. -/
theorem infₛ_eq_argmin_on (hs : s.Nonempty) :
    infₛ s = argminOn id (@IsWellFounded.wf α (· < ·) _) s hs :=
  IsLeast.cinfₛ_eq ⟨argminOn_mem _ _ _ _, fun a ha => argminOn_le id _ _ ha⟩
#align Inf_eq_argmin_on infₛ_eq_argmin_on

/- warning: is_least_Inf -> isLeast_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))], (Set.Nonempty.{u1} α s) -> (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9007 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9009 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9007 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9009)], (Set.Nonempty.{u1} α s) -> (IsLeast.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align is_least_Inf isLeast_cinfₛₓ'. -/
theorem isLeast_cinfₛ (hs : s.Nonempty) : IsLeast s (infₛ s) :=
  by
  rw [infₛ_eq_argmin_on hs]
  exact ⟨argmin_on_mem _ _ _ _, fun a ha => argmin_on_le id _ _ ha⟩
#align is_least_Inf isLeast_cinfₛ

/- warning: le_cInf_iff' -> le_cinfₛ_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))], (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9097 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9099 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9097 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9099)], (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) b (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) s)))
Case conversion may be inaccurate. Consider using '#align le_cInf_iff' le_cinfₛ_iff'ₓ'. -/
theorem le_cinfₛ_iff' (hs : s.Nonempty) : b ≤ infₛ s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (isLeast_cinfₛ hs).IsGLB
#align le_cInf_iff' le_cinfₛ_iff'

/- warning: Inf_mem -> cinfₛ_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))], (Set.Nonempty.{u1} α s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9152 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9154 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9152 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9154)], (Set.Nonempty.{u1} α s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s) s)
Case conversion may be inaccurate. Consider using '#align Inf_mem cinfₛ_memₓ'. -/
theorem cinfₛ_mem (hs : s.Nonempty) : infₛ s ∈ s :=
  (isLeast_cinfₛ hs).1
#align Inf_mem cinfₛ_mem

/- warning: infi_mem -> cinfᵢ_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))] [_inst_3 : Nonempty.{u2} ι] (f : ι -> α), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f) (Set.range.{u1, u2} α ι f)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9197 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9199 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9197 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9199)] [_inst_3 : Nonempty.{u2} ι] (f : ι -> α), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) ι f) (Set.range.{u1, u2} α ι f)
Case conversion may be inaccurate. Consider using '#align infi_mem cinfᵢ_memₓ'. -/
theorem cinfᵢ_mem [Nonempty ι] (f : ι → α) : infᵢ f ∈ range f :=
  cinfₛ_mem (range_nonempty f)
#align infi_mem cinfᵢ_mem

/- warning: monotone_on.map_Inf -> MonotoneOn.map_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))] {β : Type.{u2}} [_inst_3 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (MonotoneOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_3)))) f s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_3) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9251 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9253 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9251 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9253)] {β : Type.{u2}} [_inst_3 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (MonotoneOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_3)))) f s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_3) (Set.image.{u1, u2} α β f s)))
Case conversion may be inaccurate. Consider using '#align monotone_on.map_Inf MonotoneOn.map_cinfₛₓ'. -/
theorem MonotoneOn.map_cinfₛ {β : Type _} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (infₛ s) = infₛ (f '' s) :=
  (hf.map_isLeast (isLeast_cinfₛ hs)).cinfₛ_eq.symm
#align monotone_on.map_Inf MonotoneOn.map_cinfₛ

/- warning: monotone.map_Inf -> Monotone.map_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))))] {β : Type.{u2}} [_inst_3 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_3)))) f) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_3) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} α] {s : Set.{u1} α} [_inst_2 : IsWellOrder.{u1} α (fun (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9323 : α) (x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9325 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9323 x._@.Mathlib.Order.ConditionallyCompleteLattice.Basic._hyg.9325)] {β : Type.{u2}} [_inst_3 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_3)))) f) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_3) (Set.image.{u1, u2} α β f s)))
Case conversion may be inaccurate. Consider using '#align monotone.map_Inf Monotone.map_cinfₛₓ'. -/
theorem Monotone.map_cinfₛ {β : Type _} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : Monotone f) (hs : s.Nonempty) : f (infₛ s) = infₛ (f '' s) :=
  (hf.map_isLeast (isLeast_cinfₛ hs)).cinfₛ_eq.symm
#align monotone.map_Inf Monotone.map_cinfₛ

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `nonempty`/`set.nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α]

/- warning: cSup_empty -> csupₛ_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α], Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α], Eq.{succ u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cSup_empty csupₛ_emptyₓ'. -/
@[simp]
theorem csupₛ_empty : (supₛ ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.cSup_empty
#align cSup_empty csupₛ_empty

/- warning: csupr_of_empty -> csupᵢ_of_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align csupr_of_empty csupᵢ_of_emptyₓ'. -/
@[simp]
theorem csupᵢ_of_empty [IsEmpty ι] (f : ι → α) : (⨆ i, f i) = ⊥ := by
  rw [supᵢ_of_empty', csupₛ_empty]
#align csupr_of_empty csupᵢ_of_empty

/- warning: csupr_false -> csupᵢ_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : False -> α), Eq.{succ u1} α (supᵢ.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) False (fun (i : False) => f i)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : False -> α), Eq.{succ u1} α (supᵢ.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) False (fun (i : False) => f i)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align csupr_false csupᵢ_falseₓ'. -/
@[simp]
theorem csupᵢ_false (f : False → α) : (⨆ i, f i) = ⊥ :=
  csupᵢ_of_empty f
#align csupr_false csupᵢ_false

/- warning: cInf_univ -> cinfₛ_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α], Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) (Set.univ.{u1} α)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α], Eq.{succ u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) (Set.univ.{u1} α)) (Bot.bot.{u1} α (ConditionallyCompleteLinearOrderBot.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align cInf_univ cinfₛ_univₓ'. -/
@[simp]
theorem cinfₛ_univ : infₛ (univ : Set α) = ⊥ :=
  isLeast_univ.cinfₛ_eq
#align cInf_univ cinfₛ_univ

/- warning: is_lub_cSup' -> isLUB_csupₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align is_lub_cSup' isLUB_csupₛ'ₓ'. -/
theorem isLUB_csupₛ' {s : Set α} (hs : BddAbove s) : IsLUB s (supₛ s) :=
  by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csupₛ_empty, isLUB_empty]
  · exact isLUB_csupₛ hne hs
#align is_lub_cSup' isLUB_csupₛ'

/- warning: cSup_le_iff' -> csupₛ_le_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (forall {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) x a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (forall {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) x a)))
Case conversion may be inaccurate. Consider using '#align cSup_le_iff' csupₛ_le_iff'ₓ'. -/
theorem csupₛ_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : supₛ s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (isLUB_csupₛ' hs)
#align cSup_le_iff' csupₛ_le_iff'

/- warning: cSup_le' -> csupₛ_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a)
Case conversion may be inaccurate. Consider using '#align cSup_le' csupₛ_le'ₓ'. -/
theorem csupₛ_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : supₛ s ≤ a :=
  (csupₛ_le_iff' ⟨a, h⟩).2 h
#align cSup_le' csupₛ_le'

/- warning: le_cSup_iff' -> le_csupₛ_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_cSup_iff' le_csupₛ_iff'ₓ'. -/
theorem le_csupₛ_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ supₛ s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h b hb => le_trans h (csupₛ_le' hb), fun hb => hb _ fun x => le_csupₛ h⟩
#align le_cSup_iff' le_csupₛ_iff'

/- warning: le_csupr_iff' -> le_csupᵢ_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : ι -> α} {a : α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u2} α ι s)) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι s)) (forall (b : α), (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (s i) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {s : ι -> α} {a : α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u1} α ι s)) -> (Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) a (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι s)) (forall (b : α), (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (s i) b) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_csupr_iff' le_csupᵢ_iff'ₓ'. -/
theorem le_csupᵢ_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ supᵢ s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [supᵢ, h, le_csupₛ_iff', upperBounds]
#align le_csupr_iff' le_csupᵢ_iff'

/- warning: le_cInf_iff'' -> le_cinfₛ_iff'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Set.Nonempty.{u1} α s) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align le_cInf_iff'' le_cinfₛ_iff''ₓ'. -/
theorem le_cinfₛ_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a ≤ infₛ s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_cinfₛ_iff ⟨⊥, fun a _ => bot_le⟩ Ne
#align le_cInf_iff'' le_cinfₛ_iff''

/- warning: le_cinfi_iff' -> le_cinfᵢ_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (f i))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (f i))
Case conversion may be inaccurate. Consider using '#align le_cinfi_iff' le_cinfᵢ_iff'ₓ'. -/
theorem le_cinfᵢ_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ infᵢ f ↔ ∀ i, a ≤ f i :=
  le_cinfᵢ_iff ⟨⊥, fun a _ => bot_le⟩
#align le_cinfi_iff' le_cinfᵢ_iff'

/- warning: cInf_le' -> cinfₛ_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) a)
Case conversion may be inaccurate. Consider using '#align cInf_le' cinfₛ_le'ₓ'. -/
theorem cinfₛ_le' {s : Set α} {a : α} (h : a ∈ s) : infₛ s ≤ a :=
  cinfₛ_le ⟨⊥, fun a _ => bot_le⟩ h
#align cInf_le' cinfₛ_le'

/- warning: cinfi_le' -> cinfᵢ_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (infᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι f) (f i)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (infᵢ.{u2, u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι f) (f i)
Case conversion may be inaccurate. Consider using '#align cinfi_le' cinfᵢ_le'ₓ'. -/
theorem cinfᵢ_le' (f : ι → α) (i : ι) : infᵢ f ≤ f i :=
  cinfᵢ_le ⟨⊥, fun a _ => bot_le⟩ _
#align cinfi_le' cinfᵢ_le'

/- warning: exists_lt_of_lt_cSup' -> exists_lt_of_lt_csupₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) -> (Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) -> (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_lt_cSup' exists_lt_of_lt_csupₛ'ₓ'. -/
theorem exists_lt_of_lt_csupₛ' {s : Set α} {a : α} (h : a < supₛ s) : ∃ b ∈ s, a < b :=
  by
  contrapose! h
  exact csupₛ_le' h
#align exists_lt_of_lt_cSup' exists_lt_of_lt_csupₛ'

/- warning: csupr_le_iff' -> csupᵢ_le_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u2} α ι f)) -> (forall {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (f i) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {f : ι -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u1} α ι f)) -> (forall {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι (fun (i : ι) => f i)) a) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align csupr_le_iff' csupᵢ_le_iff'ₓ'. -/
theorem csupᵢ_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    (⨆ i, f i) ≤ a ↔ ∀ i, f i ≤ a :=
  (csupₛ_le_iff' h).trans forall_range_iff
#align csupr_le_iff' csupᵢ_le_iff'

/- warning: csupr_le' -> csupᵢ_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (f i) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (f i) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι (fun (i : ι) => f i)) a)
Case conversion may be inaccurate. Consider using '#align csupr_le' csupᵢ_le'ₓ'. -/
theorem csupᵢ_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆ i, f i) ≤ a :=
  csupₛ_le' <| forall_range_iff.2 h
#align csupr_le' csupᵢ_le'

/- warning: exists_lt_of_lt_csupr' -> exists_lt_of_lt_csupᵢ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {f : ι -> α} {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι (fun (i : ι) => f i))) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) a (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {f : ι -> α} {a : α}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) a (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι (fun (i : ι) => f i))) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) a (f i)))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_lt_csupr' exists_lt_of_lt_csupᵢ'ₓ'. -/
theorem exists_lt_of_lt_csupᵢ' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i :=
  by
  contrapose! h
  exact csupᵢ_le' h
#align exists_lt_of_lt_csupr' exists_lt_of_lt_csupᵢ'

/- warning: csupr_mono' -> csupᵢ_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {ι' : Sort.{u3}} {f : ι -> α} {g : ι' -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u3} α ι' g)) -> (forall (i : ι), Exists.{u3} ι' (fun (i' : ι') => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (f i) (g i'))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (supᵢ.{u1, u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι f) (supᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) ι' g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] {ι' : Sort.{u3}} {f : ι -> α} {g : ι' -> α}, (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u3} α ι' g)) -> (forall (i : ι), Exists.{u3} ι' (fun (i' : ι') => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (f i) (g i'))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))))))) (supᵢ.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι f) (supᵢ.{u2, u3} α (ConditionallyCompleteLattice.toSupSet.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1))) ι' g))
Case conversion may be inaccurate. Consider using '#align csupr_mono' csupᵢ_mono'ₓ'. -/
theorem csupᵢ_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : supᵢ f ≤ supᵢ g :=
  csupᵢ_le' fun i => Exists.elim (h i) (le_csupᵢ_of_le hg)
#align csupr_mono' csupᵢ_mono'

/- warning: cInf_le_cInf' -> cinfₛ_le_cinfₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) t))
Case conversion may be inaccurate. Consider using '#align cInf_le_cInf' cinfₛ_le_cinfₛ'ₓ'. -/
theorem cinfₛ_le_cinfₛ' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : infₛ s ≤ infₛ t :=
  cinfₛ_le_cinfₛ (OrderBot.bddBelow s) h₁ h₂
#align cInf_le_cInf' cinfₛ_le_cinfₛ'

end ConditionallyCompleteLinearOrderBot

namespace WithTop

open Classical

variable [ConditionallyCompleteLinearOrderBot α]

/- warning: with_top.is_lub_Sup' -> WithTop.isLUB_supₛ' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : ConditionallyCompleteLattice.{u1} β] {s : Set.{u1} (WithTop.{u1} β)}, (Set.Nonempty.{u1} (WithTop.{u1} β) s) -> (IsLUB.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s (SupSet.supₛ.{u1} (WithTop.{u1} β) (WithTop.hasSup.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (ConditionallyCompleteLattice.toHasSup.{u1} β _inst_2)) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : ConditionallyCompleteLattice.{u1} β] {s : Set.{u1} (WithTop.{u1} β)}, (Set.Nonempty.{u1} (WithTop.{u1} β) s) -> (IsLUB.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s (SupSet.supₛ.{u1} (WithTop.{u1} β) (instSupSetWithTop.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align with_top.is_lub_Sup' WithTop.isLUB_supₛ'ₓ'. -/
/-- The Sup of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem isLUB_supₛ' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (supₛ s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply some_le_some.2
      exact le_csupₛ h_1 ha
    · intro _ _
      exact le_top
  · show ite _ _ _ ∈ _
    split_ifs
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine' some_le_some.2 (csupₛ_le _ _)
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
#align with_top.is_lub_Sup' WithTop.isLUB_supₛ'

/- warning: with_top.is_lub_Sup -> WithTop.isLUB_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (s : Set.{u1} (WithTop.{u1} α)), IsLUB.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) s (SupSet.supₛ.{u1} (WithTop.{u1} α) (WithTop.hasSup.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (s : Set.{u1} (WithTop.{u1} α)), IsLUB.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) s (SupSet.supₛ.{u1} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align with_top.is_lub_Sup WithTop.isLUB_supₛₓ'. -/
theorem isLUB_supₛ (s : Set (WithTop α)) : IsLUB s (supₛ s) :=
  by
  cases' s.eq_empty_or_nonempty with hs hs
  · rw [hs]
    show IsLUB ∅ (ite _ _ _)
    split_ifs
    · cases h
    · rw [preimage_empty, csupₛ_empty]
      exact isLUB_empty
    · exfalso
      apply h_1
      use ⊥
      rintro a ⟨⟩
  exact is_lub_Sup' hs
#align with_top.is_lub_Sup WithTop.isLUB_supₛ

/- warning: with_top.is_glb_Inf' -> WithTop.isGLB_infₛ' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : ConditionallyCompleteLattice.{u1} β] {s : Set.{u1} (WithTop.{u1} β)}, (BddBelow.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s) -> (IsGLB.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s (InfSet.infₛ.{u1} (WithTop.{u1} β) (WithTop.hasInf.{u1} β (ConditionallyCompleteLattice.toHasInf.{u1} β _inst_2)) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : ConditionallyCompleteLattice.{u1} β] {s : Set.{u1} (WithTop.{u1} β)}, (BddBelow.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s) -> (IsGLB.{u1} (WithTop.{u1} β) (WithTop.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) s (InfSet.infₛ.{u1} (WithTop.{u1} β) (instInfSetWithTop.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align with_top.is_glb_Inf' WithTop.isGLB_infₛ'ₓ'. -/
/-- The Inf of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem isGLB_infₛ' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (infₛ s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine' some_le_some.2 (cinfₛ_le _ ha)
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
      · refine' some_le_some.2 (le_cinfₛ _ _)
        ·
          classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (h ⟨a, ha⟩).elim
        · intro b hb
          rw [← some_le_some]
          exact ha hb
#align with_top.is_glb_Inf' WithTop.isGLB_infₛ'

/- warning: with_top.is_glb_Inf -> WithTop.isGLB_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (s : Set.{u1} (WithTop.{u1} α)), IsGLB.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) s (InfSet.infₛ.{u1} (WithTop.{u1} α) (WithTop.hasInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (s : Set.{u1} (WithTop.{u1} α)), IsGLB.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))))))) s (InfSet.infₛ.{u1} (WithTop.{u1} α) (instInfSetWithTop.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align with_top.is_glb_Inf WithTop.isGLB_infₛₓ'. -/
theorem isGLB_infₛ (s : Set (WithTop α)) : IsGLB s (infₛ s) :=
  by
  by_cases hs : BddBelow s
  · exact is_glb_Inf' hs
  · exfalso
    apply hs
    use ⊥
    intro _ _
    exact bot_le
#align with_top.is_glb_Inf WithTop.isGLB_infₛ

noncomputable instance : CompleteLinearOrder (WithTop α) :=
  { WithTop.linearOrder, WithTop.lattice, WithTop.orderTop,
    WithTop.orderBot with
    supₛ := supₛ
    le_sup := fun s => (isLUB_supₛ s).1
    sup_le := fun s => (isLUB_supₛ s).2
    infₛ := infₛ
    le_inf := fun s => (isGLB_infₛ s).2
    inf_le := fun s => (isGLB_infₛ s).1 }

/- warning: with_top.coe_Sup -> WithTop.coe_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (supᵢ.{u1, succ u1} (WithTop.{u1} α) (WithTop.hasSup.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) α (fun (a : α) => supᵢ.{u1, 0} (WithTop.{u1} α) (WithTop.hasSup.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) s) -> (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (supᵢ.{u1, succ u1} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) α (fun (a : α) => supᵢ.{u1, 0} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => WithTop.some.{u1} α a))))
Case conversion may be inaccurate. Consider using '#align with_top.coe_Sup WithTop.coe_supₛₓ'. -/
/-- A version of `with_top.coe_Sup'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_supₛ {s : Set α} (hb : BddAbove s) : ↑(supₛ s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_Sup' hb, supₛ_image]
#align with_top.coe_Sup WithTop.coe_supₛ

/- warning: with_top.coe_Inf -> WithTop.coe_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (infᵢ.{u1, succ u1} (WithTop.{u1} α) (WithTop.hasInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) α (fun (a : α) => infᵢ.{u1, 0} (WithTop.{u1} α) (WithTop.hasInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1))) s)) (infᵢ.{u1, succ u1} (WithTop.{u1} α) (instInfSetWithTop.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) α (fun (a : α) => infᵢ.{u1, 0} (WithTop.{u1} α) (instInfSetWithTop.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => WithTop.some.{u1} α a))))
Case conversion may be inaccurate. Consider using '#align with_top.coe_Inf WithTop.coe_infₛₓ'. -/
/-- A version of `with_top.coe_Inf'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_infₛ {s : Set α} (hs : s.Nonempty) : ↑(infₛ s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_Inf' hs, infₛ_image]
#align with_top.coe_Inf WithTop.coe_infₛ

end WithTop

namespace Monotone

variable [Preorder α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`Sup` and `Inf`. -/


/- warning: monotone.le_cSup_image -> Monotone.le_csupₛ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α} {c : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) -> (BddAbove.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (f c) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) f) -> (forall {s : Set.{u2} α} {c : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c s) -> (BddAbove.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (f c) (SupSet.supₛ.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.image.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align monotone.le_cSup_image Monotone.le_csupₛ_imageₓ'. -/
theorem le_csupₛ_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ supₛ (f '' s) :=
  le_csupₛ (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)
#align monotone.le_cSup_image Monotone.le_csupₛ_image

/- warning: monotone.cSup_image_le -> Monotone.csupₛ_image_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {B : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) B (upperBounds.{u1} α _inst_1 s)) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β f s)) (f B))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) f) -> (forall {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall {B : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) B (upperBounds.{u2} α _inst_1 s)) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (SupSet.supₛ.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.image.{u2, u1} α β f s)) (f B))))
Case conversion may be inaccurate. Consider using '#align monotone.cSup_image_le Monotone.csupₛ_image_leₓ'. -/
theorem csupₛ_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    supₛ (f '' s) ≤ f B :=
  csupₛ_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)
#align monotone.cSup_image_le Monotone.csupₛ_image_le

/- warning: monotone.cInf_image_le -> Monotone.cinfₛ_image_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α} {c : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) -> (BddBelow.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (Set.image.{u1, u2} α β f s)) (f c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) f) -> (forall {s : Set.{u2} α} {c : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c s) -> (BddBelow.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) (Set.image.{u2, u1} α β f s)) (f c)))
Case conversion may be inaccurate. Consider using '#align monotone.cInf_image_le Monotone.cinfₛ_image_leₓ'. -/
theorem cinfₛ_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) :
    infₛ (f '' s) ≤ f c :=
  @le_csupₛ_image αᵒᵈ βᵒᵈ _ _ _ (fun x y hxy => h_mono hxy) _ _ hcs h_bdd
#align monotone.cInf_image_le Monotone.cinfₛ_image_le

/- warning: monotone.le_cInf_image -> Monotone.le_cinfₛ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {B : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) B (lowerBounds.{u1} α _inst_1 s)) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (f B) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (Set.image.{u1, u2} α β f s)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) f) -> (forall {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall {B : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) B (lowerBounds.{u2} α _inst_1 s)) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (f B) (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) (Set.image.{u2, u1} α β f s)))))
Case conversion may be inaccurate. Consider using '#align monotone.le_cInf_image Monotone.le_cinfₛ_imageₓ'. -/
theorem le_cinfₛ_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ lowerBounds s) :
    f B ≤ infₛ (f '' s) :=
  @csupₛ_image_le αᵒᵈ βᵒᵈ _ _ _ (fun x y hxy => h_mono hxy) _ hs _ hB
#align monotone.le_cInf_image Monotone.le_cinfₛ_image

end Monotone

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

/- warning: galois_connection.l_cSup -> GaloisConnection.l_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (l (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (supᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => l ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) l u) -> (forall {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} β (l (SupSet.supₛ.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (supᵢ.{u1, succ u2} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => l (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)))))
Case conversion may be inaccurate. Consider using '#align galois_connection.l_cSup GaloisConnection.l_csupₛₓ'. -/
theorem l_csupₛ (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (supₛ s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.csupᵢ_set_eq (gc.isLUB_l_image <| isLUB_csupₛ hne hbdd) hne
#align galois_connection.l_cSup GaloisConnection.l_csupₛ

/- warning: galois_connection.l_cSup' -> GaloisConnection.l_csupₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (l (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β l s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) l u) -> (forall {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} β (l (SupSet.supₛ.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (SupSet.supₛ.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.image.{u2, u1} α β l s))))
Case conversion may be inaccurate. Consider using '#align galois_connection.l_cSup' GaloisConnection.l_csupₛ'ₓ'. -/
theorem l_csupₛ' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (supₛ s) = supₛ (l '' s) := by rw [gc.l_cSup hne hbdd, supₛ_image']
#align galois_connection.l_cSup' GaloisConnection.l_csupₛ'

/- warning: galois_connection.l_csupr -> GaloisConnection.l_csupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι f)) -> (Eq.{succ u2} β (l (supᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i))) (supᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) ι (fun (i : ι) => l (f i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u1} ι] {l : α -> β} {u : β -> α}, (GaloisConnection.{u3, u2} α β (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {f : ι -> α}, (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.range.{u3, u1} α ι f)) -> (Eq.{succ u2} β (l (supᵢ.{u3, u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i))) (supᵢ.{u2, u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) ι (fun (i : ι) => l (f i)))))
Case conversion may be inaccurate. Consider using '#align galois_connection.l_csupr GaloisConnection.l_csupᵢₓ'. -/
theorem l_csupᵢ (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [supᵢ, gc.l_cSup (range_nonempty _) hf, supᵢ_range']
#align galois_connection.l_csupr GaloisConnection.l_csupᵢ

/- warning: galois_connection.l_csupr_set -> GaloisConnection.l_csupᵢ_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u3} γ} {f : γ -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u3, u1} γ α f s)) -> (Set.Nonempty.{u3} γ s) -> (Eq.{succ u2} β (l (supᵢ.{u1, succ u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))) (supᵢ.{u2, succ u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => l (f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u3, u2} α β (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u1} γ} {f : γ -> α}, (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.image.{u1, u3} γ α f s)) -> (Set.Nonempty.{u1} γ s) -> (Eq.{succ u2} β (l (supᵢ.{u3, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (supᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => l (f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i))))))
Case conversion may be inaccurate. Consider using '#align galois_connection.l_csupr_set GaloisConnection.l_csupᵢ_setₓ'. -/
theorem l_csupᵢ_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) :=
  by
  haveI := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_csupr hf
#align galois_connection.l_csupr_set GaloisConnection.l_csupᵢ_set

/- warning: galois_connection.u_cInf -> GaloisConnection.u_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u2} β}, (Set.Nonempty.{u2} β s) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) s) -> (Eq.{succ u1} α (u (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) s)) (infᵢ.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) => u ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s))))) x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) l u) -> (forall {s : Set.{u1} β}, (Set.Nonempty.{u1} β s) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) s) -> (Eq.{succ u2} α (u (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) s)) (infᵢ.{u2, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) (Set.Elem.{u1} β s) (fun (x : Set.Elem.{u1} β s) => u (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) x)))))
Case conversion may be inaccurate. Consider using '#align galois_connection.u_cInf GaloisConnection.u_cinfₛₓ'. -/
theorem u_cinfₛ (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (infₛ s) = ⨅ x : s, u x :=
  gc.dual.l_csupₛ hne hbdd
#align galois_connection.u_cInf GaloisConnection.u_cinfₛ

/- warning: galois_connection.u_cInf' -> GaloisConnection.u_cinfₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u2} β}, (Set.Nonempty.{u2} β s) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) s) -> (Eq.{succ u1} α (u (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) s)) (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (Set.image.{u2, u1} β α u s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) l u) -> (forall {s : Set.{u1} β}, (Set.Nonempty.{u1} β s) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) s) -> (Eq.{succ u2} α (u (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) s)) (InfSet.infₛ.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) (Set.image.{u1, u2} β α u s))))
Case conversion may be inaccurate. Consider using '#align galois_connection.u_cInf' GaloisConnection.u_cinfₛ'ₓ'. -/
theorem u_cinfₛ' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (infₛ s) = infₛ (u '' s) :=
  gc.dual.l_csupₛ' hne hbdd
#align galois_connection.u_cInf' GaloisConnection.u_cinfₛ'

/- warning: galois_connection.u_cinfi -> GaloisConnection.u_cinfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {f : ι -> β}, (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (Set.range.{u2, u3} β ι f)) -> (Eq.{succ u1} α (u (infᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) ι (fun (i : ι) => f i))) (infᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => u (f i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u1} ι] {l : α -> β} {u : β -> α}, (GaloisConnection.{u3, u2} α β (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {f : ι -> β}, (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (Set.range.{u2, u1} β ι f)) -> (Eq.{succ u3} α (u (infᵢ.{u2, u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) ι (fun (i : ι) => f i))) (infᵢ.{u3, u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => u (f i)))))
Case conversion may be inaccurate. Consider using '#align galois_connection.u_cinfi GaloisConnection.u_cinfᵢₓ'. -/
theorem u_cinfᵢ (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_csupᵢ hf
#align galois_connection.u_cinfi GaloisConnection.u_cinfᵢ

/- warning: galois_connection.u_cinfi_set -> GaloisConnection.u_cinfᵢ_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u3} γ} {f : γ -> β}, (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (Set.image.{u3, u2} γ β f s)) -> (Set.Nonempty.{u3} γ s) -> (Eq.{succ u1} α (u (infᵢ.{u2, succ u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))) (infᵢ.{u1, succ u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => u (f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {l : α -> β} {u : β -> α}, (GaloisConnection.{u3, u2} α β (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) l u) -> (forall {s : Set.{u1} γ} {f : γ -> β}, (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (Set.image.{u1, u2} γ β f s)) -> (Set.Nonempty.{u1} γ s) -> (Eq.{succ u3} α (u (infᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (infᵢ.{u3, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => u (f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i))))))
Case conversion may be inaccurate. Consider using '#align galois_connection.u_cinfi_set GaloisConnection.u_cinfᵢ_setₓ'. -/
theorem u_cinfᵢ_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_csupᵢ_set hf hne
#align galois_connection.u_cinfi_set GaloisConnection.u_cinfᵢ_set

end GaloisConnection

namespace OrderIso

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

/- warning: order_iso.map_cSup -> OrderIso.map_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (supᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] (e : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))))) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (SupSet.supₛ.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (SupSet.supₛ.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (supᵢ.{u1, succ u2} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cSup OrderIso.map_csupₛₓ'. -/
theorem map_csupₛ (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (supₛ s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csupₛ hne hbdd
#align order_iso.map_cSup OrderIso.map_csupₛ

/- warning: order_iso.map_cSup' -> OrderIso.map_csupₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] (e : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))))) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (SupSet.supₛ.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (SupSet.supₛ.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s)) (SupSet.supₛ.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e))) s)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cSup' OrderIso.map_csupₛ'ₓ'. -/
theorem map_csupₛ' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (supₛ s) = supₛ (e '' s) :=
  e.to_galoisConnection.l_csupₛ' hne hbdd
#align order_iso.map_cSup' OrderIso.map_csupₛ'

/- warning: order_iso.map_csupr -> OrderIso.map_csupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {f : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι f)) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (supᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => f i))) (supᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (f i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u1} ι] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {f : ι -> α}, (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.range.{u3, u1} α ι f)) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (supᵢ.{u3, u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (supᵢ.{u3, u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i))) (supᵢ.{u2, u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) ι (fun (i : ι) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (f i))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_csupr OrderIso.map_csupᵢₓ'. -/
theorem map_csupᵢ (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_csupᵢ hf
#align order_iso.map_csupr OrderIso.map_csupᵢ

/- warning: order_iso.map_csupr_set -> OrderIso.map_csupᵢ_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u3} γ} {f : γ -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u3, u1} γ α f s)) -> (Set.Nonempty.{u3} γ s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (supᵢ.{u1, succ u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))) (supᵢ.{u2, succ u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} γ} {f : γ -> α}, (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.image.{u1, u3} γ α f s)) -> (Set.Nonempty.{u1} γ s) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (supᵢ.{u3, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (supᵢ.{u3, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (supᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_csupr_set OrderIso.map_csupᵢ_setₓ'. -/
theorem map_csupᵢ_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_csupᵢ_set hf hne
#align order_iso.map_csupr_set OrderIso.map_csupᵢ_set

/- warning: order_iso.map_cInf -> OrderIso.map_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) (infᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] (e : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))))) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (InfSet.infₛ.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (InfSet.infₛ.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s)) (infᵢ.{u1, succ u2} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cInf OrderIso.map_cinfₛₓ'. -/
theorem map_cinfₛ (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (infₛ s) = ⨅ x : s, e x :=
  e.dual.map_csupₛ hne hbdd
#align order_iso.map_cInf OrderIso.map_cinfₛ

/- warning: order_iso.map_cInf' -> OrderIso.map_cinfₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] (e : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))))) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (InfSet.infₛ.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (InfSet.infₛ.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s)) (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e))) s)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cInf' OrderIso.map_cinfₛ'ₓ'. -/
theorem map_cinfₛ' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (infₛ s) = infₛ (e '' s) :=
  e.dual.map_csupₛ' hne hbdd
#align order_iso.map_cInf' OrderIso.map_cinfₛ'

/- warning: order_iso.map_cinfi -> OrderIso.map_cinfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {f : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι f)) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (infᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => f i))) (infᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (f i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u1} ι] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {f : ι -> α}, (BddBelow.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.range.{u3, u1} α ι f)) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (infᵢ.{u3, u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => f i))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (infᵢ.{u3, u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => f i))) (infᵢ.{u2, u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) ι (fun (i : ι) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (f i))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cinfi OrderIso.map_cinfᵢₓ'. -/
theorem map_cinfᵢ (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_csupᵢ hf
#align order_iso.map_cinfi OrderIso.map_cinfᵢ

/- warning: order_iso.map_cinfi_set -> OrderIso.map_cinfᵢ_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u3} γ} {f : γ -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.image.{u3, u1} γ α f s)) -> (Set.Nonempty.{u3} γ s) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (infᵢ.{u1, succ u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))) (infᵢ.{u2, succ u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))))) e (f ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) s) γ (coeSubtype.{succ u3} γ (fun (x : γ) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s))))) i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))))) {s : Set.{u1} γ} {f : γ -> α}, (BddBelow.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (Set.image.{u1, u3} γ α f s)) -> (Set.Nonempty.{u1} γ s) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (infᵢ.{u3, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (infᵢ.{u3, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))) (infᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) (Set.Elem.{u1} γ s) (fun (i : Set.Elem.{u1} γ s) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) (RelEmbedding.toEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)) (f (Subtype.val.{succ u1} γ (fun (x : γ) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) i)))))
Case conversion may be inaccurate. Consider using '#align order_iso.map_cinfi_set OrderIso.map_cinfᵢ_setₓ'. -/
theorem map_cinfᵢ_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_csupᵢ_set hf hne
#align order_iso.map_cinfi_set OrderIso.map_cinfᵢ_set

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

/- warning: cSup_image2_eq_cSup_cSup -> csupₛ_image2_eq_csupₛ_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u1, u3} α γ (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (u₁ b)) -> (forall (a : α), GaloisConnection.{u2, u3} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (l a) (u₂ a)) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (SupSet.supₛ.{u3} γ (ConditionallyCompleteLattice.toHasSup.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ l s t)) (l (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u2} γ] {s : Set.{u3} α} {t : Set.{u1} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} α γ (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.swap.{succ u3, succ u1, succ u2} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (u₁ b)) -> (forall (a : α), GaloisConnection.{u1, u2} β γ (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (l a) (u₂ a)) -> (Set.Nonempty.{u3} α s) -> (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u2} γ (SupSet.supₛ.{u2} γ (ConditionallyCompleteLattice.toSupSet.{u2} γ _inst_3) (Set.image2.{u3, u1, u2} α β γ l s t)) (l (SupSet.supₛ.{u3} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) s) (SupSet.supₛ.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cSup_image2_eq_cSup_cSup csupₛ_image2_eq_csupₛ_csupₛₓ'. -/
theorem csupₛ_image2_eq_csupₛ_csupₛ (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : supₛ (image2 l s t) = l (supₛ s) (supₛ t) :=
  by
  refine' eq_of_forall_ge_iff fun c => _
  rw [csupₛ_le_iff (hs₁.image2 (fun _ => (h₁ _).monotone_l) (fun _ => (h₂ _).monotone_l) ht₁)
      (hs₀.image2 ht₀),
    forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, csupₛ_le_iff ht₁ ht₀]
  simp_rw [← (h₂ _).le_iff_le, (h₁ _).le_iff_le, csupₛ_le_iff hs₁ hs₀]
#align cSup_image2_eq_cSup_cSup csupₛ_image2_eq_csupₛ_csupₛ

/- warning: cSup_image2_eq_cSup_cInf -> csupₛ_image2_eq_csupₛ_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u1, u3} α γ (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (u₁ b)) -> (forall (a : α), GaloisConnection.{u2, u3} (OrderDual.{u2} β) γ (OrderDual.preorder.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} β) β γ (l a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β))) (Function.comp.{succ u3, succ u2, succ u2} γ β (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β)) (u₂ a))) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (SupSet.supₛ.{u3} γ (ConditionallyCompleteLattice.toHasSup.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ l s t)) (l (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u2} γ] {s : Set.{u3} α} {t : Set.{u1} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} α γ (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.swap.{succ u3, succ u1, succ u2} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (u₁ b)) -> (forall (a : α), GaloisConnection.{u1, u2} (OrderDual.{u1} β) γ (OrderDual.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.comp.{succ u1, succ u1, succ u2} (OrderDual.{u1} β) β γ (l a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β))) (Function.comp.{succ u2, succ u1, succ u1} γ β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) (u₂ a))) -> (Set.Nonempty.{u3} α s) -> (BddAbove.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u2} γ (SupSet.supₛ.{u2} γ (ConditionallyCompleteLattice.toSupSet.{u2} γ _inst_3) (Set.image2.{u3, u1, u2} α β γ l s t)) (l (SupSet.supₛ.{u3} α (ConditionallyCompleteLattice.toSupSet.{u3} α _inst_1) s) (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cSup_image2_eq_cSup_cInf csupₛ_image2_eq_csupₛ_cinfₛₓ'. -/
theorem csupₛ_image2_eq_csupₛ_cinfₛ (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → supₛ (image2 l s t) = l (supₛ s) (infₛ t) :=
  @csupₛ_image2_eq_csupₛ_csupₛ _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cSup_cInf csupₛ_image2_eq_csupₛ_cinfₛ

/- warning: cSup_image2_eq_cInf_cSup -> csupₛ_image2_eq_cinfₛ_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u1, u3} (OrderDual.{u1} α) γ (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} α) α γ (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α))) (Function.comp.{succ u3, succ u1, succ u1} γ α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) (u₁ b))) -> (forall (a : α), GaloisConnection.{u2, u3} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (l a) (u₂ a)) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (SupSet.supₛ.{u3} γ (ConditionallyCompleteLattice.toHasSup.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ l s t)) (l (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u2} γ] {s : Set.{u3} α} {t : Set.{u1} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} (OrderDual.{u3} α) γ (OrderDual.preorder.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.comp.{succ u3, succ u3, succ u2} (OrderDual.{u3} α) α γ (Function.swap.{succ u3, succ u1, succ u2} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.{u3} α) (fun (_x : OrderDual.{u3} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u3} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.ofDual.{u3} α))) (Function.comp.{succ u2, succ u3, succ u3} γ α (OrderDual.{u3} α) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} α (OrderDual.{u3} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u3} α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} α (OrderDual.{u3} α)) (OrderDual.toDual.{u3} α)) (u₁ b))) -> (forall (a : α), GaloisConnection.{u1, u2} β γ (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (l a) (u₂ a)) -> (Set.Nonempty.{u3} α s) -> (BddBelow.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u2} γ (SupSet.supₛ.{u2} γ (ConditionallyCompleteLattice.toSupSet.{u2} γ _inst_3) (Set.image2.{u3, u1, u2} α β γ l s t)) (l (InfSet.infₛ.{u3} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) s) (SupSet.supₛ.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cSup_image2_eq_cInf_cSup csupₛ_image2_eq_cinfₛ_csupₛₓ'. -/
theorem csupₛ_image2_eq_cinfₛ_csupₛ (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → supₛ (image2 l s t) = l (infₛ s) (supₛ t) :=
  @csupₛ_image2_eq_csupₛ_csupₛ αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cSup csupₛ_image2_eq_cinfₛ_csupₛ

/- warning: cSup_image2_eq_cInf_cInf -> csupₛ_image2_eq_cinfₛ_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u1, u3} (OrderDual.{u1} α) γ (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} α) α γ (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α))) (Function.comp.{succ u3, succ u1, succ u1} γ α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) (u₁ b))) -> (forall (a : α), GaloisConnection.{u2, u3} (OrderDual.{u2} β) γ (OrderDual.preorder.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} β) β γ (l a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β))) (Function.comp.{succ u3, succ u2, succ u2} γ β (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β)) (u₂ a))) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (SupSet.supₛ.{u3} γ (ConditionallyCompleteLattice.toHasSup.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ l s t)) (l (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u3} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u2} γ] {s : Set.{u3} α} {t : Set.{u1} β} {l : α -> β -> γ} {u₁ : β -> γ -> α} {u₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} (OrderDual.{u3} α) γ (OrderDual.preorder.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1))))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.comp.{succ u3, succ u3, succ u2} (OrderDual.{u3} α) α γ (Function.swap.{succ u3, succ u1, succ u2} α β (fun (ᾰ : α) (ᾰ : β) => γ) l b) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.{u3} α) (fun (_x : OrderDual.{u3} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u3} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.ofDual.{u3} α))) (Function.comp.{succ u2, succ u3, succ u3} γ α (OrderDual.{u3} α) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} α (OrderDual.{u3} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u3} α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} α (OrderDual.{u3} α)) (OrderDual.toDual.{u3} α)) (u₁ b))) -> (forall (a : α), GaloisConnection.{u1, u2} (OrderDual.{u1} β) γ (OrderDual.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (ConditionallyCompleteLattice.toLattice.{u2} γ _inst_3)))) (Function.comp.{succ u1, succ u1, succ u2} (OrderDual.{u1} β) β γ (l a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β))) (Function.comp.{succ u2, succ u1, succ u1} γ β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) (u₂ a))) -> (Set.Nonempty.{u3} α s) -> (BddBelow.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α (Lattice.toSemilatticeInf.{u3} α (ConditionallyCompleteLattice.toLattice.{u3} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u2} γ (SupSet.supₛ.{u2} γ (ConditionallyCompleteLattice.toSupSet.{u2} γ _inst_3) (Set.image2.{u3, u1, u2} α β γ l s t)) (l (InfSet.infₛ.{u3} α (ConditionallyCompleteLattice.toInfSet.{u3} α _inst_1) s) (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cSup_image2_eq_cInf_cInf csupₛ_image2_eq_cinfₛ_cinfₛₓ'. -/
theorem csupₛ_image2_eq_cinfₛ_cinfₛ (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → supₛ (image2 l s t) = l (infₛ s) (infₛ t) :=
  @csupₛ_image2_eq_csupₛ_csupₛ αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cInf csupₛ_image2_eq_cinfₛ_cinfₛ

/- warning: cInf_image2_eq_cInf_cInf -> cinfₛ_image2_eq_cinfₛ_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u1} γ α (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (l₁ b) (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b)) -> (forall (a : α), GaloisConnection.{u3, u2} γ β (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (l₂ a) (u a)) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.infₛ.{u3} γ (ConditionallyCompleteLattice.toHasInf.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ u s t)) (u (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u2} α} {t : Set.{u1} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} γ α (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (l₁ b) (Function.swap.{succ u2, succ u1, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b)) -> (forall (a : α), GaloisConnection.{u3, u1} γ β (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (l₂ a) (u a)) -> (Set.Nonempty.{u2} α s) -> (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.infₛ.{u3} γ (ConditionallyCompleteLattice.toInfSet.{u3} γ _inst_3) (Set.image2.{u2, u1, u3} α β γ u s t)) (u (InfSet.infₛ.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s) (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cInf_image2_eq_cInf_cInf cinfₛ_image2_eq_cinfₛ_cinfₛₓ'. -/
theorem cinfₛ_image2_eq_cinfₛ_cinfₛ (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → infₛ (image2 u s t) = u (infₛ s) (infₛ t) :=
  @csupₛ_image2_eq_csupₛ_csupₛ αᵒᵈ βᵒᵈ γᵒᵈ _ _ _ _ _ _ l₁ l₂ (fun _ => (h₁ _).dual) fun _ =>
    (h₂ _).dual
#align cInf_image2_eq_cInf_cInf cinfₛ_image2_eq_cinfₛ_cinfₛ

/- warning: cInf_image2_eq_cInf_cSup -> cinfₛ_image2_eq_cinfₛ_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u1} γ α (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (l₁ b) (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b)) -> (forall (a : α), GaloisConnection.{u3, u2} γ (OrderDual.{u2} β) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (Function.comp.{succ u3, succ u2, succ u2} γ β (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β)) (l₂ a)) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} β) β γ (u a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β)))) -> (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.infₛ.{u3} γ (ConditionallyCompleteLattice.toHasInf.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ u s t)) (u (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u2} α} {t : Set.{u1} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} γ α (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) (l₁ b) (Function.swap.{succ u2, succ u1, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b)) -> (forall (a : α), GaloisConnection.{u3, u1} γ (OrderDual.{u1} β) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (Function.comp.{succ u3, succ u1, succ u1} γ β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) (l₂ a)) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} β) β γ (u a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β)))) -> (Set.Nonempty.{u2} α s) -> (BddBelow.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.infₛ.{u3} γ (ConditionallyCompleteLattice.toInfSet.{u3} γ _inst_3) (Set.image2.{u2, u1, u3} α β γ u s t)) (u (InfSet.infₛ.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) s) (SupSet.supₛ.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cInf_image2_eq_cInf_cSup cinfₛ_image2_eq_cinfₛ_csupₛₓ'. -/
theorem cinfₛ_image2_eq_cinfₛ_csupₛ (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → infₛ (image2 u s t) = u (infₛ s) (supₛ t) :=
  @cinfₛ_image2_eq_cinfₛ_cinfₛ _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cInf_cSup cinfₛ_image2_eq_cinfₛ_csupₛ

/- warning: cInf_image2_eq_cSup_cInf -> cinfₛ_image2_eq_csupₛ_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u1} γ (OrderDual.{u1} α) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Function.comp.{succ u3, succ u1, succ u1} γ α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) (l₁ b)) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} α) α γ (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)))) -> (forall (a : α), GaloisConnection.{u3, u2} γ β (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) (l₂ a) (u a)) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.infₛ.{u3} γ (ConditionallyCompleteLattice.toHasInf.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ u s t)) (u (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u2} α} {t : Set.{u1} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} γ (OrderDual.{u2} α) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Function.comp.{succ u3, succ u2, succ u2} γ α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) (l₁ b)) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} α) α γ (Function.swap.{succ u2, succ u1, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α)))) -> (forall (a : α), GaloisConnection.{u3, u1} γ β (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) (l₂ a) (u a)) -> (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.infₛ.{u3} γ (ConditionallyCompleteLattice.toInfSet.{u3} γ _inst_3) (Set.image2.{u2, u1, u3} α β γ u s t)) (u (SupSet.supₛ.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s) (InfSet.infₛ.{u1} β (ConditionallyCompleteLattice.toInfSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cInf_image2_eq_cSup_cInf cinfₛ_image2_eq_csupₛ_cinfₛₓ'. -/
theorem cinfₛ_image2_eq_csupₛ_cinfₛ (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → infₛ (image2 u s t) = u (supₛ s) (infₛ t) :=
  @cinfₛ_image2_eq_cinfₛ_cinfₛ αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cInf cinfₛ_image2_eq_csupₛ_cinfₛ

/- warning: cInf_image2_eq_cSup_cSup -> cinfₛ_image2_eq_csupₛ_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u1} α} {t : Set.{u2} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u1} γ (OrderDual.{u1} α) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (Function.comp.{succ u3, succ u1, succ u1} γ α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) (l₁ b)) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} α) α γ (Function.swap.{succ u1, succ u2, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)))) -> (forall (a : α), GaloisConnection.{u3, u2} γ (OrderDual.{u2} β) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2))))) (Function.comp.{succ u3, succ u2, succ u2} γ β (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β)) (l₂ a)) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} β) β γ (u a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β)))) -> (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u2} β t) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.infₛ.{u3} γ (ConditionallyCompleteLattice.toHasInf.{u3} γ _inst_3) (Set.image2.{u1, u2, u3} α β γ u s t)) (u (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] [_inst_2 : ConditionallyCompleteLattice.{u1} β] [_inst_3 : ConditionallyCompleteLattice.{u3} γ] {s : Set.{u2} α} {t : Set.{u1} β} {u : α -> β -> γ} {l₁ : β -> γ -> α} {l₂ : α -> γ -> β}, (forall (b : β), GaloisConnection.{u3, u2} γ (OrderDual.{u2} α) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (Function.comp.{succ u3, succ u2, succ u2} γ α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) (l₁ b)) (Function.comp.{succ u2, succ u2, succ u3} (OrderDual.{u2} α) α γ (Function.swap.{succ u2, succ u1, succ u3} α β (fun (ᾰ : α) (ᾰ : β) => γ) u b) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α)))) -> (forall (a : α), GaloisConnection.{u3, u1} γ (OrderDual.{u1} β) (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (ConditionallyCompleteLattice.toLattice.{u3} γ _inst_3)))) (OrderDual.preorder.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2))))) (Function.comp.{succ u3, succ u1, succ u1} γ β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) (l₂ a)) (Function.comp.{succ u1, succ u1, succ u3} (OrderDual.{u1} β) β γ (u a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β)))) -> (Set.Nonempty.{u2} α s) -> (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1)))) s) -> (Set.Nonempty.{u1} β t) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (ConditionallyCompleteLattice.toLattice.{u1} β _inst_2)))) t) -> (Eq.{succ u3} γ (InfSet.infₛ.{u3} γ (ConditionallyCompleteLattice.toInfSet.{u3} γ _inst_3) (Set.image2.{u2, u1, u3} α β γ u s t)) (u (SupSet.supₛ.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) s) (SupSet.supₛ.{u1} β (ConditionallyCompleteLattice.toSupSet.{u1} β _inst_2) t)))
Case conversion may be inaccurate. Consider using '#align cInf_image2_eq_cSup_cSup cinfₛ_image2_eq_csupₛ_csupₛₓ'. -/
theorem cinfₛ_image2_eq_csupₛ_csupₛ (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → infₛ (image2 u s t) = u (supₛ s) (supₛ t) :=
  @cinfₛ_image2_eq_cinfₛ_cinfₛ αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cSup cinfₛ_image2_eq_csupₛ_csupₛ

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
    le_cSup := fun S a hS haS => (WithTop.isLUB_supₛ' ⟨a, haS⟩).1 haS
    cSup_le := fun S a hS haS => (WithTop.isLUB_supₛ' hS).2 haS
    cInf_le := fun S a hS haS => (WithTop.isGLB_infₛ' hS).1 haS
    le_cInf := fun S a hS haS => (WithTop.isGLB_infₛ' ⟨a, haS⟩).2 haS }
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
    le_sup := fun S a haS => (WithTop.isLUB_supₛ' ⟨a, haS⟩).1 haS
    sup_le := fun S a ha => by
      cases' S.eq_empty_or_nonempty with h
      · show ite _ _ _ ≤ a
        split_ifs
        · rw [h] at h_1
          cases h_1
        · convert bot_le
          convert WithBot.supₛ_empty
          rw [h]
          rfl
        · exfalso
          apply h_2
          use ⊥
          rw [h]
          rintro b ⟨⟩
      · refine' (WithTop.isLUB_supₛ' h).2 ha
    inf_le := fun S a haS =>
      show ite _ _ _ ≤ a by
        split_ifs
        · cases' a with a
          exact le_rfl
          cases h haS <;> tauto
        · cases a
          · exact le_top
          · apply WithTop.some_le_some.2
            refine' cinfₛ_le _ haS
            use ⊥
            intro b hb
            exact bot_le
    le_inf := fun S a haS => (WithTop.isGLB_infₛ' ⟨a, haS⟩).2 haS }
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

/- warning: with_top.supr_coe_eq_top -> WithTop.supr_coe_eq_top is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] (f : ι -> α), Iff (Eq.{succ u2} (WithTop.{u2} α) (supᵢ.{u2, u1} (WithTop.{u2} α) (WithTop.hasSup.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))) ι (fun (x : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) α (WithTop.{u2} α) (HasLiftT.mk.{succ u2, succ u2} α (WithTop.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} α (WithTop.{u2} α) (WithTop.hasCoeT.{u2} α))) (f x))) (Top.top.{u2} (WithTop.{u2} α) (WithTop.hasTop.{u2} α))) (Not (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u1} α ι f)))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : ι -> α), Iff (Eq.{succ u1} (WithTop.{u1} α) (supᵢ.{u1, u2} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) ι (fun (x : ι) => WithTop.some.{u1} α (f x))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (Not (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u2} α ι f)))
Case conversion may be inaccurate. Consider using '#align with_top.supr_coe_eq_top WithTop.supr_coe_eq_topₓ'. -/
theorem WithTop.supr_coe_eq_top {ι : Sort _} {α : Type _} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : (⨆ x, (f x : WithTop α)) = ⊤ ↔ ¬BddAbove (Set.range f) :=
  by
  rw [supᵢ_eq_top, not_bddAbove_iff]
  refine' ⟨fun hf r => _, fun hf a ha => _⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, with_top.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using with_top.coe_lt_coe.mpr hi⟩
#align with_top.supr_coe_eq_top WithTop.supr_coe_eq_top

/- warning: with_top.supr_coe_lt_top -> WithTop.supr_coe_lt_top is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u2} α] (f : ι -> α), Iff (LT.lt.{u2} (WithTop.{u2} α) (Preorder.toLT.{u2} (WithTop.{u2} α) (WithTop.preorder.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))))) (supᵢ.{u2, u1} (WithTop.{u2} α) (WithTop.hasSup.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (ConditionallyCompleteLattice.toHasSup.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))) ι (fun (x : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) α (WithTop.{u2} α) (HasLiftT.mk.{succ u2, succ u2} α (WithTop.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} α (WithTop.{u2} α) (WithTop.hasCoeT.{u2} α))) (f x))) (Top.top.{u2} (WithTop.{u2} α) (WithTop.hasTop.{u2} α))) (BddAbove.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} α _inst_1)))))) (Set.range.{u2, u1} α ι f))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrderBot.{u1} α] (f : ι -> α), Iff (LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))))) (supᵢ.{u1, u2} (WithTop.{u1} α) (instSupSetWithTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (ConditionallyCompleteLattice.toSupSet.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))) ι (fun (x : ι) => WithTop.some.{u1} α (f x))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} α (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u1} α _inst_1)))))) (Set.range.{u1, u2} α ι f))
Case conversion may be inaccurate. Consider using '#align with_top.supr_coe_lt_top WithTop.supr_coe_lt_topₓ'. -/
theorem WithTop.supr_coe_lt_top {ι : Sort _} {α : Type _} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : (⨆ x, (f x : WithTop α)) < ⊤ ↔ BddAbove (Set.range f) :=
  lt_top_iff_ne_top.trans <| (WithTop.supr_coe_eq_top f).Not.trans Classical.not_not
#align with_top.supr_coe_lt_top WithTop.supr_coe_lt_top

end WithTopBot

-- Guard against import creep
assert_not_exists Multiset

