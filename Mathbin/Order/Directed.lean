/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.directed
! leanprover-community/mathlib commit e8cf0cfec5fcab9baf46dc17d30c5e22048468be
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image
import Mathbin.Order.Lattice
import Mathbin.Order.Max
import Mathbin.Order.Bounds.Basic

/-!
# Directed indexed families and sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `directed_on r s`: Predicate stating that the set `s` is `r`-directed.
* `is_directed α r`: Prop-valued mixin stating that `α` is `r`-directed. Follows the style of the
  unbundled relation classes such as `is_total`.
* `scott_continuous`: Predicate stating that a function between preorders preserves
  `is_lub` on directed sets.

## References
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
-/


open Function

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} (r r' s : α → α → Prop)

-- mathport name: «expr ≼ »
local infixl:50 " ≼ " => r

#print Directed /-
/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def Directed (f : ι → α) :=
  ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z
#align directed Directed
-/

#print DirectedOn /-
/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def DirectedOn (s : Set α) :=
  ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s, x ≼ z ∧ y ≼ z
#align directed_on DirectedOn
-/

variable {r r'}

#print directedOn_iff_directed /-
theorem directedOn_iff_directed {s} : @DirectedOn α r s ↔ Directed r (coe : s → α) := by
  simp [Directed, DirectedOn] <;> refine' ball_congr fun x hx => by simp <;> rfl
#align directed_on_iff_directed directedOn_iff_directed
-/

alias directedOn_iff_directed ↔ DirectedOn.directed_val _
#align directed_on.directed_coe DirectedOn.directed_val

#print directedOn_range /-
theorem directedOn_range {f : ι → α} : Directed r f ↔ DirectedOn r (Set.range f) := by
  simp_rw [Directed, DirectedOn, Set.forall_range_iff, Set.exists_range_iff]
#align directed_on_range directedOn_range
-/

#print directedOn_image /-
theorem directedOn_image {s} {f : β → α} : DirectedOn r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s := by
  simp only [DirectedOn, Set.ball_image_iff, Set.bex_image_iff, Order.Preimage]
#align directed_on_image directedOn_image
-/

#print DirectedOn.mono' /-
theorem DirectedOn.mono' {s : Set α} (hs : DirectedOn r s)
    (h : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b → r' a b) : DirectedOn r' s := fun x hx y hy =>
  let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  ⟨z, hz, h hx hz hxz, h hy hz hyz⟩
#align directed_on.mono' DirectedOn.mono'
-/

#print DirectedOn.mono /-
theorem DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : ∀ {a b}, r a b → r' a b) :
    DirectedOn r' s :=
  h.mono' fun _ _ _ _ => H
#align directed_on.mono DirectedOn.mono
-/

/- warning: directed_comp -> directed_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {ι : Sort.{u3}} {f : ι -> β} {g : β -> α}, Iff (Directed.{u1, u3} α ι r (Function.comp.{u3, succ u2, succ u1} ι β α g f)) (Directed.{u2, u3} β ι (Order.Preimage.{succ u2, succ u1} β α g r) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {r : α -> α -> Prop} {ι : Sort.{u1}} {f : ι -> β} {g : β -> α}, Iff (Directed.{u2, u1} α ι r (Function.comp.{u1, succ u3, succ u2} ι β α g f)) (Directed.{u3, u1} β ι (Order.Preimage.{succ u3, succ u2} β α g r) f)
Case conversion may be inaccurate. Consider using '#align directed_comp directed_compₓ'. -/
theorem directed_comp {ι} {f : ι → β} {g : β → α} : Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f :=
  Iff.rfl
#align directed_comp directed_comp

/- warning: directed.mono -> Directed.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : α -> α -> Prop} {ι : Sort.{u2}} {f : ι -> α}, (forall (a : α) (b : α), (r a b) -> (s a b)) -> (Directed.{u1, u2} α ι r f) -> (Directed.{u1, u2} α ι s f)
but is expected to have type
  forall {α : Type.{u2}} {r : α -> α -> Prop} {s : α -> α -> Prop} {ι : Sort.{u1}} {f : ι -> α}, (forall (a : α) (b : α), (r a b) -> (s a b)) -> (Directed.{u2, u1} α ι r f) -> (Directed.{u2, u1} α ι s f)
Case conversion may be inaccurate. Consider using '#align directed.mono Directed.monoₓ'. -/
theorem Directed.mono {s : α → α → Prop} {ι} {f : ι → α} (H : ∀ a b, r a b → s a b)
    (h : Directed r f) : Directed s f := fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩
#align directed.mono Directed.mono

/- warning: directed.mono_comp -> Directed.mono_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> α -> Prop) {ι : Sort.{u3}} {rb : β -> β -> Prop} {g : α -> β} {f : ι -> α}, (forall {{x : α}} {{y : α}}, (r x y) -> (rb (g x) (g y))) -> (Directed.{u1, u3} α ι r f) -> (Directed.{u2, u3} β ι rb (Function.comp.{u3, succ u1, succ u2} ι α β g f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} (r : α -> α -> Prop) {ι : Sort.{u1}} {rb : β -> β -> Prop} {g : α -> β} {f : ι -> α}, (forall {{x : α}} {{y : α}}, (r x y) -> (rb (g x) (g y))) -> (Directed.{u2, u1} α ι r f) -> (Directed.{u3, u1} β ι rb (Function.comp.{u1, succ u2, succ u3} ι α β g f))
Case conversion may be inaccurate. Consider using '#align directed.mono_comp Directed.mono_compₓ'. -/
theorem Directed.mono_comp {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
    (hg : ∀ ⦃x y⦄, x ≼ y → rb (g x) (g y)) (hf : Directed r f) : Directed rb (g ∘ f) :=
  directed_comp.2 <| hf.mono hg
#align directed.mono_comp Directed.mono_comp

/- warning: directed_of_sup -> directed_of_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {f : α -> β} {r : β -> β -> Prop}, (forall {{i : α}} {{j : α}}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) i j) -> (r (f i) (f j))) -> (Directed.{u2, succ u1} β α r f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {f : α -> β} {r : β -> β -> Prop}, (forall {{i : α}} {{j : α}}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) i j) -> (r (f i) (f j))) -> (Directed.{u2, succ u1} β α r f)
Case conversion may be inaccurate. Consider using '#align directed_of_sup directed_of_supₓ'. -/
/-- A monotone function on a sup-semilattice is directed. -/
theorem directed_of_sup [SemilatticeSup α] {f : α → β} {r : β → β → Prop}
    (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) : Directed r f := fun a b =>
  ⟨a ⊔ b, H le_sup_left, H le_sup_right⟩
#align directed_of_sup directed_of_sup

/- warning: monotone.directed_le -> Monotone.directed_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) _inst_2 f) -> (Directed.{u2, succ u1} β α (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) _inst_2 f) -> (Directed.{u2, succ u1} β α (fun (x._@.Mathlib.Order.Directed._hyg.1126 : β) (x._@.Mathlib.Order.Directed._hyg.1128 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Directed._hyg.1126 x._@.Mathlib.Order.Directed._hyg.1128) f)
Case conversion may be inaccurate. Consider using '#align monotone.directed_le Monotone.directed_leₓ'. -/
theorem Monotone.directed_le [SemilatticeSup α] [Preorder β] {f : α → β} :
    Monotone f → Directed (· ≤ ·) f :=
  directed_of_sup
#align monotone.directed_le Monotone.directed_le

/- warning: antitone.directed_ge -> Antitone.directed_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) _inst_2 f) -> (Directed.{u2, succ u1} β α (GE.ge.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) _inst_2 f) -> (Directed.{u2, succ u1} β α (fun (x._@.Mathlib.Order.Directed._hyg.1179 : β) (x._@.Mathlib.Order.Directed._hyg.1181 : β) => GE.ge.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Directed._hyg.1179 x._@.Mathlib.Order.Directed._hyg.1181) f)
Case conversion may be inaccurate. Consider using '#align antitone.directed_ge Antitone.directed_geₓ'. -/
theorem Antitone.directed_ge [SemilatticeSup α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Directed (· ≥ ·) f :=
  directed_of_sup hf
#align antitone.directed_ge Antitone.directed_ge

/- warning: directed_on_of_sup_mem -> directedOn_of_sup_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {S : Set.{u1} α}, (forall {{i : α}} {{j : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i S) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j S) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) i j) S)) -> (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) S)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] {S : Set.{u1} α}, (forall {{i : α}} {{j : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i S) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j S) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) i j) S)) -> (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.1249 : α) (x._@.Mathlib.Order.Directed._hyg.1251 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Directed._hyg.1249 x._@.Mathlib.Order.Directed._hyg.1251) S)
Case conversion may be inaccurate. Consider using '#align directed_on_of_sup_mem directedOn_of_sup_memₓ'. -/
/-- A set stable by supremum is `≤`-directed. -/
theorem directedOn_of_sup_mem [SemilatticeSup α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊔ j ∈ S) : DirectedOn (· ≤ ·) S := fun a ha b hb =>
  ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩
#align directed_on_of_sup_mem directedOn_of_sup_mem

/- warning: directed.extend_bot -> Directed.extend_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1)] {e : ι -> β} {f : ι -> α}, (Directed.{u1, u3} α ι (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f) -> (Function.Injective.{u3, succ u2} ι β e) -> (Directed.{u1, succ u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Function.extend.{u3, succ u2, succ u1} ι β α e f (Bot.bot.{max u2 u1} (β -> α) (Pi.hasBot.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1) _inst_2)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] {e : ι -> β} {f : ι -> α}, (Directed.{u1, u3} α ι (fun (x._@.Mathlib.Order.Directed._hyg.1323 : α) (x._@.Mathlib.Order.Directed._hyg.1325 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.1323 x._@.Mathlib.Order.Directed._hyg.1325) f) -> (Function.Injective.{u3, succ u2} ι β e) -> (Directed.{u1, succ u2} α β (fun (x._@.Mathlib.Order.Directed._hyg.1342 : α) (x._@.Mathlib.Order.Directed._hyg.1344 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.1342 x._@.Mathlib.Order.Directed._hyg.1344) (Function.extend.{u3, succ u2, succ u1} ι β α e f (Bot.bot.{max u1 u2} (β -> α) (Pi.instBotForAll.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))))
Case conversion may be inaccurate. Consider using '#align directed.extend_bot Directed.extend_botₓ'. -/
theorem Directed.extend_bot [Preorder α] [OrderBot α] {e : ι → β} {f : ι → α}
    (hf : Directed (· ≤ ·) f) (he : Function.Injective e) :
    Directed (· ≤ ·) (Function.extend e f ⊥) :=
  by
  intro a b
  rcases(em (∃ i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  · use b; simp [Function.extend_apply' _ _ _ ha]
  rcases(em (∃ i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  · use e i; simp [Function.extend_apply' _ _ _ hb]
  rcases hf i j with ⟨k, hi, hj⟩
  use e k
  simp only [he.extend_apply, *, true_and_iff]
#align directed.extend_bot Directed.extend_bot

/- warning: directed_of_inf -> directed_of_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {r : β -> β -> Prop} {f : α -> β}, (forall (a₁ : α) (a₂ : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a₁ a₂) -> (r (f a₂) (f a₁))) -> (Directed.{u2, succ u1} β α r f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {r : β -> β -> Prop} {f : α -> β}, (forall (a₁ : α) (a₂ : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a₁ a₂) -> (r (f a₂) (f a₁))) -> (Directed.{u2, succ u1} β α r f)
Case conversion may be inaccurate. Consider using '#align directed_of_inf directed_of_infₓ'. -/
/-- An antitone function on an inf-semilattice is directed. -/
theorem directed_of_inf [SemilatticeInf α] {r : β → β → Prop} {f : α → β}
    (hf : ∀ a₁ a₂, a₁ ≤ a₂ → r (f a₂) (f a₁)) : Directed r f := fun x y =>
  ⟨x ⊓ y, hf _ _ inf_le_left, hf _ _ inf_le_right⟩
#align directed_of_inf directed_of_inf

/- warning: monotone.directed_ge -> Monotone.directed_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) _inst_2 f) -> (Directed.{u2, succ u1} β α (GE.ge.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) _inst_2 f) -> (Directed.{u2, succ u1} β α (fun (x._@.Mathlib.Order.Directed._hyg.1627 : β) (x._@.Mathlib.Order.Directed._hyg.1629 : β) => GE.ge.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Directed._hyg.1627 x._@.Mathlib.Order.Directed._hyg.1629) f)
Case conversion may be inaccurate. Consider using '#align monotone.directed_ge Monotone.directed_geₓ'. -/
theorem Monotone.directed_ge [SemilatticeInf α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Directed (· ≥ ·) f :=
  directed_of_inf hf
#align monotone.directed_ge Monotone.directed_ge

/- warning: antitone.directed_le -> Antitone.directed_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) _inst_2 f) -> (Directed.{u2, succ u1} β α (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) _inst_2 f) -> (Directed.{u2, succ u1} β α (fun (x._@.Mathlib.Order.Directed._hyg.1681 : β) (x._@.Mathlib.Order.Directed._hyg.1683 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Directed._hyg.1681 x._@.Mathlib.Order.Directed._hyg.1683) f)
Case conversion may be inaccurate. Consider using '#align antitone.directed_le Antitone.directed_leₓ'. -/
theorem Antitone.directed_le [SemilatticeInf α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Directed (· ≤ ·) f :=
  directed_of_inf hf
#align antitone.directed_le Antitone.directed_le

/- warning: directed_on_of_inf_mem -> directedOn_of_inf_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {S : Set.{u1} α}, (forall {{i : α}} {{j : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i S) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j S) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) i j) S)) -> (DirectedOn.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) S)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] {S : Set.{u1} α}, (forall {{i : α}} {{j : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i S) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j S) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) i j) S)) -> (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.1751 : α) (x._@.Mathlib.Order.Directed._hyg.1753 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Directed._hyg.1751 x._@.Mathlib.Order.Directed._hyg.1753) S)
Case conversion may be inaccurate. Consider using '#align directed_on_of_inf_mem directedOn_of_inf_memₓ'. -/
/-- A set stable by infimum is `≥`-directed. -/
theorem directedOn_of_inf_mem [SemilatticeInf α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊓ j ∈ S) : DirectedOn (· ≥ ·) S := fun a ha b hb =>
  ⟨a ⊓ b, H ha hb, inf_le_left, inf_le_right⟩
#align directed_on_of_inf_mem directedOn_of_inf_mem

#print IsDirected /-
/-- `is_directed α r` states that for any elements `a`, `b` there exists an element `c` such that
`r a c` and `r b c`. -/
class IsDirected (α : Type _) (r : α → α → Prop) : Prop where
  Directed (a b : α) : ∃ c, r a c ∧ r b c
#align is_directed IsDirected
-/

#print directed_of /-
theorem directed_of (r : α → α → Prop) [IsDirected α r] (a b : α) : ∃ c, r a c ∧ r b c :=
  IsDirected.directed _ _
#align directed_of directed_of
-/

#print directed_id /-
theorem directed_id [IsDirected α r] : Directed r id := by convert directed_of r
#align directed_id directed_id
-/

#print directed_id_iff /-
theorem directed_id_iff : Directed r id ↔ IsDirected α r :=
  ⟨fun h => ⟨h⟩, @directed_id _ _⟩
#align directed_id_iff directed_id_iff
-/

#print directedOn_univ /-
theorem directedOn_univ [IsDirected α r] : DirectedOn r Set.univ := fun a _ b _ =>
  let ⟨c, hc⟩ := directed_of r a b
  ⟨c, trivial, hc⟩
#align directed_on_univ directedOn_univ
-/

#print directedOn_univ_iff /-
theorem directedOn_univ_iff : DirectedOn r Set.univ ↔ IsDirected α r :=
  ⟨fun h =>
    ⟨fun a b =>
      let ⟨c, _, hc⟩ := h a trivial b trivial
      ⟨c, hc⟩⟩,
    @directedOn_univ _ _⟩
#align directed_on_univ_iff directedOn_univ_iff
-/

#print IsTotal.to_isDirected /-
-- see Note [lower instance priority]
instance (priority := 100) IsTotal.to_isDirected [IsTotal α r] : IsDirected α r :=
  ⟨fun a b => Or.cases_on (total_of r a b) (fun h => ⟨b, h, refl _⟩) fun h => ⟨a, refl _, h⟩⟩
#align is_total.to_is_directed IsTotal.to_isDirected
-/

#print isDirected_mono /-
theorem isDirected_mono [IsDirected α r] (h : ∀ ⦃a b⦄, r a b → s a b) : IsDirected α s :=
  ⟨fun a b =>
    let ⟨c, ha, hb⟩ := IsDirected.directed a b
    ⟨c, h ha, h hb⟩⟩
#align is_directed_mono isDirected_mono
-/

#print exists_ge_ge /-
theorem exists_ge_ge [LE α] [IsDirected α (· ≤ ·)] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  directed_of (· ≤ ·) a b
#align exists_ge_ge exists_ge_ge
-/

#print exists_le_le /-
theorem exists_le_le [LE α] [IsDirected α (· ≥ ·)] (a b : α) : ∃ c, c ≤ a ∧ c ≤ b :=
  directed_of (· ≥ ·) a b
#align exists_le_le exists_le_le
-/

#print OrderDual.isDirected_ge /-
instance OrderDual.isDirected_ge [LE α] [IsDirected α (· ≤ ·)] : IsDirected αᵒᵈ (· ≥ ·) := by
  assumption
#align order_dual.is_directed_ge OrderDual.isDirected_ge
-/

#print OrderDual.isDirected_le /-
instance OrderDual.isDirected_le [LE α] [IsDirected α (· ≥ ·)] : IsDirected αᵒᵈ (· ≤ ·) := by
  assumption
#align order_dual.is_directed_le OrderDual.isDirected_le
-/

section Reflexive

/- warning: directed_on.insert -> DirectedOn.insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop}, (Reflexive.{succ u1} α r) -> (forall (a : α) {s : Set.{u1} α}, (DirectedOn.{u1} α r s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Exists.{succ u1} α (fun (c : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c s) => And (r a c) (r b c))))) -> (DirectedOn.{u1} α r (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop}, (Reflexive.{succ u1} α r) -> (forall (a : α) {s : Set.{u1} α}, (DirectedOn.{u1} α r s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Exists.{succ u1} α (fun (c : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) c s) (And (r a c) (r b c))))) -> (DirectedOn.{u1} α r (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)))
Case conversion may be inaccurate. Consider using '#align directed_on.insert DirectedOn.insertₓ'. -/
theorem DirectedOn.insert (h : Reflexive r) (a : α) {s : Set α} (hd : DirectedOn r s)
    (ha : ∀ b ∈ s, ∃ c ∈ s, a ≼ c ∧ b ≼ c) : DirectedOn r (insert a s) :=
  by
  rintro x (rfl | hx) y (rfl | hy)
  · exact ⟨y, Set.mem_insert _ _, h _, h _⟩
  · obtain ⟨w, hws, hwr⟩ := ha y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
  · obtain ⟨w, hws, hwr⟩ := ha x hx
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr.symm⟩
  · obtain ⟨w, hws, hwr⟩ := hd x hx y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
#align directed_on.insert DirectedOn.insert

#print directedOn_singleton /-
theorem directedOn_singleton (h : Reflexive r) (a : α) : DirectedOn r ({a} : Set α) :=
  fun x hx y hy => ⟨x, hx, h _, hx.symm ▸ hy.symm ▸ h _⟩
#align directed_on_singleton directedOn_singleton
-/

#print directedOn_pair /-
theorem directedOn_pair (h : Reflexive r) {a b : α} (hab : a ≼ b) : DirectedOn r ({a, b} : Set α) :=
  (directedOn_singleton h _).insert h _ fun c hc => ⟨c, hc, hc.symm ▸ hab, h _⟩
#align directed_on_pair directedOn_pair
-/

#print directedOn_pair' /-
theorem directedOn_pair' (h : Reflexive r) {a b : α} (hab : a ≼ b) :
    DirectedOn r ({b, a} : Set α) := by
  rw [Set.pair_comm]
  apply directedOn_pair h hab
#align directed_on_pair' directedOn_pair'
-/

end Reflexive

section Preorder

variable [Preorder α] {a : α}

/- warning: is_min.is_bot -> IsMin.isBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : IsDirected.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1))], (IsMin.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a) -> (IsBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : IsDirected.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3039 : α) (x._@.Mathlib.Order.Directed._hyg.3041 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.3039 x._@.Mathlib.Order.Directed._hyg.3041)], (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a) -> (IsBot.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_min.is_bot IsMin.isBotₓ'. -/
protected theorem IsMin.isBot [IsDirected α (· ≥ ·)] (h : IsMin a) : IsBot a := fun b =>
  let ⟨c, hca, hcb⟩ := exists_le_le a b
  (h hca).trans hcb
#align is_min.is_bot IsMin.isBot

/- warning: is_max.is_top -> IsMax.isTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : IsDirected.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1))], (IsMax.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a) -> (IsTop.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : IsDirected.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3128 : α) (x._@.Mathlib.Order.Directed._hyg.3130 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.3128 x._@.Mathlib.Order.Directed._hyg.3130)], (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a) -> (IsTop.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_max.is_top IsMax.isTopₓ'. -/
protected theorem IsMax.isTop [IsDirected α (· ≤ ·)] (h : IsMax a) : IsTop a :=
  h.toDual.IsBot
#align is_max.is_top IsMax.isTop

/- warning: directed_on.is_bot_of_is_min -> DirectedOn.is_bot_of_is_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α}, (DirectedOn.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) s) -> (forall {m : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a m) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) m a)) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) m a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α}, (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3181 : α) (x._@.Mathlib.Order.Directed._hyg.3183 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.3181 x._@.Mathlib.Order.Directed._hyg.3183) s) -> (forall {m : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) m a)) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) m a)))
Case conversion may be inaccurate. Consider using '#align directed_on.is_bot_of_is_min DirectedOn.is_bot_of_is_minₓ'. -/
theorem DirectedOn.is_bot_of_is_min {s : Set α} (hd : DirectedOn (· ≥ ·) s) {m} (hm : m ∈ s)
    (hmin : ∀ a ∈ s, a ≤ m → m ≤ a) : ∀ a ∈ s, m ≤ a := fun a as =>
  let ⟨x, xs, xm, xa⟩ := hd m hm a as
  (hmin x xs xm).trans xa
#align directed_on.is_bot_of_is_min DirectedOn.is_bot_of_is_min

/- warning: directed_on.is_top_of_is_max -> DirectedOn.is_top_of_is_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α}, (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) s) -> (forall {m : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) m a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a m)) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a m)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α}, (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3326 : α) (x._@.Mathlib.Order.Directed._hyg.3328 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.3326 x._@.Mathlib.Order.Directed._hyg.3328) s) -> (forall {m : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) m a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a m)) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a m)))
Case conversion may be inaccurate. Consider using '#align directed_on.is_top_of_is_max DirectedOn.is_top_of_is_maxₓ'. -/
theorem DirectedOn.is_top_of_is_max {s : Set α} (hd : DirectedOn (· ≤ ·) s) {m} (hm : m ∈ s)
    (hmax : ∀ a ∈ s, m ≤ a → a ≤ m) : ∀ a ∈ s, a ≤ m :=
  @DirectedOn.is_bot_of_is_min αᵒᵈ _ s hd m hm hmax
#align directed_on.is_top_of_is_max DirectedOn.is_top_of_is_max

/- warning: is_top_or_exists_gt -> isTop_or_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : IsDirected.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1))] (a : α), Or (IsTop.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a) (Exists.{succ u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : IsDirected.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3428 : α) (x._@.Mathlib.Order.Directed._hyg.3430 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.3428 x._@.Mathlib.Order.Directed._hyg.3430)] (a : α), Or (IsTop.{u1} α (Preorder.toLE.{u1} α _inst_1) a) (Exists.{succ u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align is_top_or_exists_gt isTop_or_exists_gtₓ'. -/
theorem isTop_or_exists_gt [IsDirected α (· ≤ ·)] (a : α) : IsTop a ∨ ∃ b, a < b :=
  (em (IsMax a)).imp IsMax.isTop not_isMax_iff.mp
#align is_top_or_exists_gt isTop_or_exists_gt

/- warning: is_bot_or_exists_lt -> isBot_or_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : IsDirected.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1))] (a : α), Or (IsBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a) (Exists.{succ u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_1) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : IsDirected.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3497 : α) (x._@.Mathlib.Order.Directed._hyg.3499 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.3497 x._@.Mathlib.Order.Directed._hyg.3499)] (a : α), Or (IsBot.{u1} α (Preorder.toLE.{u1} α _inst_1) a) (Exists.{succ u1} α (fun (b : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) b a))
Case conversion may be inaccurate. Consider using '#align is_bot_or_exists_lt isBot_or_exists_ltₓ'. -/
theorem isBot_or_exists_lt [IsDirected α (· ≥ ·)] (a : α) : IsBot a ∨ ∃ b, b < a :=
  @isTop_or_exists_gt αᵒᵈ _ _ a
#align is_bot_or_exists_lt isBot_or_exists_lt

/- warning: is_bot_iff_is_min -> isBot_iff_isMin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : IsDirected.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1))], Iff (IsBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a) (IsMin.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : IsDirected.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3562 : α) (x._@.Mathlib.Order.Directed._hyg.3564 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.3562 x._@.Mathlib.Order.Directed._hyg.3564)], Iff (IsBot.{u1} α (Preorder.toLE.{u1} α _inst_1) a) (IsMin.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_bot_iff_is_min isBot_iff_isMinₓ'. -/
theorem isBot_iff_isMin [IsDirected α (· ≥ ·)] : IsBot a ↔ IsMin a :=
  ⟨IsBot.isMin, IsMin.isBot⟩
#align is_bot_iff_is_min isBot_iff_isMin

/- warning: is_top_iff_is_max -> isTop_iff_isMax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : IsDirected.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1))], Iff (IsTop.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a) (IsMax.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α} [_inst_2 : IsDirected.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3615 : α) (x._@.Mathlib.Order.Directed._hyg.3617 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Directed._hyg.3615 x._@.Mathlib.Order.Directed._hyg.3617)], Iff (IsTop.{u1} α (Preorder.toLE.{u1} α _inst_1) a) (IsMax.{u1} α (Preorder.toLE.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_top_iff_is_max isTop_iff_isMaxₓ'. -/
theorem isTop_iff_isMax [IsDirected α (· ≤ ·)] : IsTop a ↔ IsMax a :=
  ⟨IsTop.isMax, IsMax.isTop⟩
#align is_top_iff_is_max isTop_iff_isMax

variable (β) [PartialOrder β]

/- warning: exists_lt_of_directed_ge -> exists_lt_of_directed_ge is a dubious translation:
lean 3 declaration is
  forall (β : Type.{u1}) [_inst_2 : PartialOrder.{u1} β] [_inst_3 : IsDirected.{u1} β (GE.ge.{u1} β (Preorder.toHasLe.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)))] [_inst_4 : Nontrivial.{u1} β], Exists.{succ u1} β (fun (a : β) => Exists.{succ u1} β (fun (b : β) => LT.lt.{u1} β (Preorder.toHasLt.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) a b))
but is expected to have type
  forall (β : Type.{u1}) [_inst_2 : PartialOrder.{u1} β] [_inst_3 : IsDirected.{u1} β (fun (x._@.Mathlib.Order.Directed._hyg.3699 : β) (x._@.Mathlib.Order.Directed._hyg.3701 : β) => GE.ge.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Directed._hyg.3699 x._@.Mathlib.Order.Directed._hyg.3701)] [_inst_4 : Nontrivial.{u1} β], Exists.{succ u1} β (fun (a : β) => Exists.{succ u1} β (fun (b : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) a b))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_directed_ge exists_lt_of_directed_geₓ'. -/
theorem exists_lt_of_directed_ge [IsDirected β (· ≥ ·)] [Nontrivial β] : ∃ a b : β, a < b :=
  by
  rcases exists_pair_ne β with ⟨a, b, hne⟩
  rcases isBot_or_exists_lt a with (ha | ⟨c, hc⟩)
  exacts[⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]
#align exists_lt_of_directed_ge exists_lt_of_directed_ge

/- warning: exists_lt_of_directed_le -> exists_lt_of_directed_le is a dubious translation:
lean 3 declaration is
  forall (β : Type.{u1}) [_inst_2 : PartialOrder.{u1} β] [_inst_3 : IsDirected.{u1} β (LE.le.{u1} β (Preorder.toHasLe.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)))] [_inst_4 : Nontrivial.{u1} β], Exists.{succ u1} β (fun (a : β) => Exists.{succ u1} β (fun (b : β) => LT.lt.{u1} β (Preorder.toHasLt.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) a b))
but is expected to have type
  forall (β : Type.{u1}) [_inst_2 : PartialOrder.{u1} β] [_inst_3 : IsDirected.{u1} β (fun (x._@.Mathlib.Order.Directed._hyg.3802 : β) (x._@.Mathlib.Order.Directed._hyg.3804 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Directed._hyg.3802 x._@.Mathlib.Order.Directed._hyg.3804)] [_inst_4 : Nontrivial.{u1} β], Exists.{succ u1} β (fun (a : β) => Exists.{succ u1} β (fun (b : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) a b))
Case conversion may be inaccurate. Consider using '#align exists_lt_of_directed_le exists_lt_of_directed_leₓ'. -/
theorem exists_lt_of_directed_le [IsDirected β (· ≤ ·)] [Nontrivial β] : ∃ a b : β, a < b :=
  let ⟨a, b, h⟩ := exists_lt_of_directed_ge βᵒᵈ
  ⟨b, a, h⟩
#align exists_lt_of_directed_le exists_lt_of_directed_le

end Preorder

/- warning: semilattice_sup.to_is_directed_le -> SemilatticeSup.to_isDirected_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α], IsDirected.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α], IsDirected.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3905 : α) (x._@.Mathlib.Order.Directed._hyg.3907 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Directed._hyg.3905 x._@.Mathlib.Order.Directed._hyg.3907)
Case conversion may be inaccurate. Consider using '#align semilattice_sup.to_is_directed_le SemilatticeSup.to_isDirected_leₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) SemilatticeSup.to_isDirected_le [SemilatticeSup α] :
    IsDirected α (· ≤ ·) :=
  ⟨fun a b => ⟨a ⊔ b, le_sup_left, le_sup_right⟩⟩
#align semilattice_sup.to_is_directed_le SemilatticeSup.to_isDirected_le

/- warning: semilattice_inf.to_is_directed_ge -> SemilatticeInf.to_isDirected_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α], IsDirected.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α], IsDirected.{u1} α (fun (x._@.Mathlib.Order.Directed._hyg.3966 : α) (x._@.Mathlib.Order.Directed._hyg.3968 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Directed._hyg.3966 x._@.Mathlib.Order.Directed._hyg.3968)
Case conversion may be inaccurate. Consider using '#align semilattice_inf.to_is_directed_ge SemilatticeInf.to_isDirected_geₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) SemilatticeInf.to_isDirected_ge [SemilatticeInf α] :
    IsDirected α (· ≥ ·) :=
  ⟨fun a b => ⟨a ⊓ b, inf_le_left, inf_le_right⟩⟩
#align semilattice_inf.to_is_directed_ge SemilatticeInf.to_isDirected_ge

#print OrderTop.to_isDirected_le /-
-- see Note [lower instance priority]
instance (priority := 100) OrderTop.to_isDirected_le [LE α] [OrderTop α] : IsDirected α (· ≤ ·) :=
  ⟨fun a b => ⟨⊤, le_top, le_top⟩⟩
#align order_top.to_is_directed_le OrderTop.to_isDirected_le
-/

#print OrderBot.to_isDirected_ge /-
-- see Note [lower instance priority]
instance (priority := 100) OrderBot.to_isDirected_ge [LE α] [OrderBot α] : IsDirected α (· ≥ ·) :=
  ⟨fun a b => ⟨⊥, bot_le, bot_le⟩⟩
#align order_bot.to_is_directed_ge OrderBot.to_isDirected_ge
-/

section ScottContinuous

variable [Preorder α] {a : α}

#print ScottContinuous /-
/-- A function between preorders is said to be Scott continuous if it preserves `is_lub` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous wrt the
Scott topology.

The dual notion

```lean
∀ ⦃d : set α⦄, d.nonempty → directed_on (≥) d → ∀ ⦃a⦄, is_glb d a → is_glb (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
def ScottContinuous [Preorder β] (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)
#align scott_continuous ScottContinuous
-/

#print ScottContinuous.monotone /-
protected theorem ScottContinuous.monotone [Preorder β] {f : α → β} (h : ScottContinuous f) :
    Monotone f := by
  intro a b hab
  have e1 : IsLUB (f '' {a, b}) (f b) := by
    apply h
    · exact Set.insert_nonempty _ _
    · exact directedOn_pair le_refl hab
    · rw [IsLUB, upperBounds_insert, upperBounds_singleton,
        Set.inter_eq_self_of_subset_right (set.Ici_subset_Ici.mpr hab)]
      exact isLeast_Ici
  apply e1.1
  rw [Set.image_pair]
  exact Set.mem_insert _ _
#align scott_continuous.monotone ScottContinuous.monotone
-/

end ScottContinuous

