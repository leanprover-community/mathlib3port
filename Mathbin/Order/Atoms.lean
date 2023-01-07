/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module order.atoms
! leanprover-community/mathlib commit 134625f523e737f650a6ea7f0c82a6177e45e622
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ModularLattice
import Mathbin.Order.WellFounded

/-!
# Atoms, Coatoms, and Simple Lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `is_atom a` indicates that the only element below `a` is `⊥`.
  * `is_coatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
  * `is_atomic` indicates that every element other than `⊥` is above an atom.
  * `is_coatomic` indicates that every element other than `⊤` is below a coatom.
  * `is_atomistic` indicates that every element is the `Sup` of a set of atoms.
  * `is_coatomistic` indicates that every element is the `Inf` of a set of coatoms.

### Simple Lattices
  * `is_simple_order` indicates that an order has only two unique elements, `⊥` and `⊤`.
  * `is_simple_order.bounded_order`
  * `is_simple_order.distrib_lattice`
  * Given an instance of `is_simple_order`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `is_simple_order.boolean_algebra`
    * `is_simple_order.complete_lattice`
    * `is_simple_order.complete_boolean_algebra`

## Main results
  * `is_atom_dual_iff_is_coatom` and `is_coatom_dual_iff_is_atom` express the (definitional) duality
   of `is_atom` and `is_coatom`.
  * `is_simple_order_iff_is_atom_top` and `is_simple_order_iff_is_coatom_bot` express the
  connection between atoms, coatoms, and simple lattices
  * `is_compl.is_atom_iff_is_coatom` and `is_compl.is_coatom_if_is_atom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
  * `is_atomic_iff_is_coatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/


variable {α β : Type _}

section Atoms

section IsAtom

section Preorder

variable [Preorder α] [OrderBot α] {a b x : α}

#print IsAtom /-
/-- An atom of an `order_bot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥
#align is_atom IsAtom
-/

#print IsAtom.Iic /-
theorem IsAtom.Iic (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, hb⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩
#align is_atom.Iic IsAtom.Iic
-/

#print IsAtom.of_isAtom_coe_Iic /-
theorem IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.Prop⟩ hba)⟩
#align is_atom.of_is_atom_coe_Iic IsAtom.of_isAtom_coe_Iic
-/

/- warning: is_atom_iff -> isAtom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] {a : α}, Iff (IsAtom.{u1} α _inst_1 _inst_2 a) (And (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (forall (b : α), (Ne.{succ u1} α b (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] {a : α}, Iff (IsAtom.{u1} α _inst_1 _inst_2 a) (And (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (forall (b : α), (Ne.{succ u1} α b (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b)))
Case conversion may be inaccurate. Consider using '#align is_atom_iff isAtom_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (b «expr ≠ » «expr⊥»()) -/
theorem isAtom_iff {a : α} : IsAtom a ↔ a ≠ ⊥ ∧ ∀ (b) (_ : b ≠ ⊥), b ≤ a → a ≤ b :=
  and_congr Iff.rfl <|
    forall_congr' fun b => by simp only [Ne.def, @not_imp_comm (b = ⊥), not_imp, lt_iff_le_not_le]
#align is_atom_iff isAtom_iff

end Preorder

variable [PartialOrder α] [OrderBot α] {a b x : α}

/- warning: is_atom.lt_iff -> IsAtom.lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α} {x : α}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x a) (Eq.{succ u1} α x (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α} {x : α}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x a) (Eq.{succ u1} α x (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_atom.lt_iff IsAtom.lt_iffₓ'. -/
theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩
#align is_atom.lt_iff IsAtom.lt_iff

/- warning: is_atom.le_iff -> IsAtom.le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α} {x : α}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x a) (Or (Eq.{succ u1} α x (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (Eq.{succ u1} α x a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α} {x : α}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x a) (Or (Eq.{succ u1} α x (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (Eq.{succ u1} α x a)))
Case conversion may be inaccurate. Consider using '#align is_atom.le_iff IsAtom.le_iffₓ'. -/
theorem IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by rw [le_iff_lt_or_eq, h.lt_iff]
#align is_atom.le_iff IsAtom.le_iff

/- warning: is_atom.Iic_eq -> IsAtom.Iic_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Eq.{succ u1} (Set.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Eq.{succ u1} (Set.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)))
Case conversion may be inaccurate. Consider using '#align is_atom.Iic_eq IsAtom.Iic_eqₓ'. -/
theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun x => h.le_iff
#align is_atom.Iic_eq IsAtom.Iic_eq

/- warning: bot_covby_iff -> bot_covby_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, Iff (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) a) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, Iff (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) a) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)
Case conversion may be inaccurate. Consider using '#align bot_covby_iff bot_covby_iffₓ'. -/
@[simp]
theorem bot_covby_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [Covby, bot_lt_iff_ne_bot, IsAtom, not_imp_not]
#align bot_covby_iff bot_covby_iff

alias bot_covby_iff ↔ Covby.is_atom IsAtom.bot_covby

end IsAtom

section IsCoatom

section Preorder

variable [Preorder α]

#print IsCoatom /-
/-- A coatom of an `order_top` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def IsCoatom [OrderTop α] (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤
#align is_coatom IsCoatom
-/

#print isCoatom_dual_iff_isAtom /-
@[simp]
theorem isCoatom_dual_iff_isAtom [OrderBot α] {a : α} : IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl
#align is_coatom_dual_iff_is_atom isCoatom_dual_iff_isAtom
-/

#print isAtom_dual_iff_isCoatom /-
@[simp]
theorem isAtom_dual_iff_isCoatom [OrderTop α] {a : α} : IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl
#align is_atom_dual_iff_is_coatom isAtom_dual_iff_isCoatom
-/

alias isCoatom_dual_iff_isAtom ↔ _ IsAtom.dual

alias isAtom_dual_iff_isCoatom ↔ _ IsCoatom.dual

variable [OrderTop α] {a x : α}

#print IsCoatom.Ici /-
theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ha.dual.IicCat hax
#align is_coatom.Ici IsCoatom.Ici
-/

#print IsCoatom.of_isCoatom_coe_Ici /-
theorem IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  @IsAtom.of_isAtom_coe_Iic αᵒᵈ _ _ x a ha
#align is_coatom.of_is_coatom_coe_Ici IsCoatom.of_isCoatom_coe_Ici
-/

/- warning: is_coatom_iff -> isCoatom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] {a : α}, Iff (IsCoatom.{u1} α _inst_1 _inst_2 a) (And (Ne.{succ u1} α a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (forall (b : α), (Ne.{succ u1} α b (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] {a : α}, Iff (IsCoatom.{u1} α _inst_1 _inst_2 a) (And (Ne.{succ u1} α a (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (forall (b : α), (Ne.{succ u1} α b (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) b a)))
Case conversion may be inaccurate. Consider using '#align is_coatom_iff isCoatom_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (b «expr ≠ » «expr⊤»()) -/
theorem isCoatom_iff {a : α} : IsCoatom a ↔ a ≠ ⊤ ∧ ∀ (b) (_ : b ≠ ⊤), a ≤ b → b ≤ a :=
  @isAtom_iff αᵒᵈ _ _ _
#align is_coatom_iff isCoatom_iff

end Preorder

variable [PartialOrder α] [OrderTop α] {a b x : α}

/- warning: is_coatom.lt_iff -> IsCoatom.lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α} {x : α}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a x) (Eq.{succ u1} α x (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α} {x : α}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a x) (Eq.{succ u1} α x (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_coatom.lt_iff IsCoatom.lt_iffₓ'. -/
theorem IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  h.dual.lt_iff
#align is_coatom.lt_iff IsCoatom.lt_iff

/- warning: is_coatom.le_iff -> IsCoatom.le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α} {x : α}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a x) (Or (Eq.{succ u1} α x (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (Eq.{succ u1} α x a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α} {x : α}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a x) (Or (Eq.{succ u1} α x (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (Eq.{succ u1} α x a)))
Case conversion may be inaccurate. Consider using '#align is_coatom.le_iff IsCoatom.le_iffₓ'. -/
theorem IsCoatom.le_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a :=
  h.dual.le_iff
#align is_coatom.le_iff IsCoatom.le_iff

/- warning: is_coatom.Ici_eq -> IsCoatom.Ici_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Eq.{succ u1} (Set.{u1} α) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) -> (Eq.{succ u1} (Set.{u1} α) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)))
Case conversion may be inaccurate. Consider using '#align is_coatom.Ici_eq IsCoatom.Ici_eqₓ'. -/
theorem IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a} :=
  h.dual.Iic_eq
#align is_coatom.Ici_eq IsCoatom.Ici_eq

/- warning: covby_top_iff -> covby_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, Iff (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, Iff (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)
Case conversion may be inaccurate. Consider using '#align covby_top_iff covby_top_iffₓ'. -/
@[simp]
theorem covby_top_iff : a ⋖ ⊤ ↔ IsCoatom a :=
  toDual_covby_toDual_iff.symm.trans bot_covby_iff
#align covby_top_iff covby_top_iff

alias covby_top_iff ↔ Covby.is_coatom IsCoatom.covby_top

end IsCoatom

section PartialOrder

variable [PartialOrder α] {a b : α}

#print Set.Ici.isAtom_iff /-
@[simp]
theorem Set.Ici.isAtom_iff {b : Set.Ici a} : IsAtom b ↔ a ⋖ b :=
  by
  rw [← bot_covby_iff]
  refine' (Set.OrdConnected.apply_covby_apply_iff (OrderEmbedding.subtype fun c => a ≤ c) _).symm
  simpa only [OrderEmbedding.subtype_apply, Subtype.range_coe_subtype] using Set.ordConnected_Ici
#align set.Ici.is_atom_iff Set.Ici.isAtom_iff
-/

#print Set.Iic.isCoatom_iff /-
@[simp]
theorem Set.Iic.isCoatom_iff {a : Set.Iic b} : IsCoatom a ↔ ↑a ⋖ b :=
  by
  rw [← covby_top_iff]
  refine' (Set.OrdConnected.apply_covby_apply_iff (OrderEmbedding.subtype fun c => c ≤ b) _).symm
  simpa only [OrderEmbedding.subtype_apply, Subtype.range_coe_subtype] using Set.ordConnected_Iic
#align set.Iic.is_coatom_iff Set.Iic.isCoatom_iff
-/

#print covby_iff_atom_Ici /-
theorem covby_iff_atom_Ici (h : a ≤ b) : a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a) := by simp
#align covby_iff_atom_Ici covby_iff_atom_Ici
-/

#print covby_iff_coatom_Iic /-
theorem covby_iff_coatom_Iic (h : a ≤ b) : a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b) := by simp
#align covby_iff_coatom_Iic covby_iff_coatom_Iic
-/

end PartialOrder

section Pairwise

/- warning: is_atom.inf_eq_bot_of_ne -> IsAtom.inf_eq_bot_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {a : α} {b : α}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) _inst_2 a) -> (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) _inst_2 b) -> (Ne.{succ u1} α a b) -> (Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {a : α} {b : α}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) _inst_2 a) -> (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) _inst_2 b) -> (Ne.{succ u1} α a b) -> (Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)))
Case conversion may be inaccurate. Consider using '#align is_atom.inf_eq_bot_of_ne IsAtom.inf_eq_bot_of_neₓ'. -/
theorem IsAtom.inf_eq_bot_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a)
    (hb : IsAtom b) (hab : a ≠ b) : a ⊓ b = ⊥ :=
  hab.not_le_or_not_le.elim (ha.lt_iff.1 ∘ inf_lt_left.2) (hb.lt_iff.1 ∘ inf_lt_right.2)
#align is_atom.inf_eq_bot_of_ne IsAtom.inf_eq_bot_of_ne

#print IsAtom.disjoint_of_ne /-
theorem IsAtom.disjoint_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a)
    (hb : IsAtom b) (hab : a ≠ b) : Disjoint a b :=
  disjoint_iff.mpr (IsAtom.inf_eq_bot_of_ne ha hb hab)
#align is_atom.disjoint_of_ne IsAtom.disjoint_of_ne
-/

/- warning: is_coatom.sup_eq_top_of_ne -> IsCoatom.sup_eq_top_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {a : α} {b : α}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) _inst_2 a) -> (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) _inst_2 b) -> (Ne.{succ u1} α a b) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {a : α} {b : α}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) _inst_2 a) -> (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) _inst_2 b) -> (Ne.{succ u1} α a b) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2)))
Case conversion may be inaccurate. Consider using '#align is_coatom.sup_eq_top_of_ne IsCoatom.sup_eq_top_of_neₓ'. -/
theorem IsCoatom.sup_eq_top_of_ne [SemilatticeSup α] [OrderTop α] {a b : α} (ha : IsCoatom a)
    (hb : IsCoatom b) (hab : a ≠ b) : a ⊔ b = ⊤ :=
  ha.dual.inf_eq_bot_of_ne hb.dual hab
#align is_coatom.sup_eq_top_of_ne IsCoatom.sup_eq_top_of_ne

end Pairwise

end Atoms

section Atomic

variable [PartialOrder α] (α)

#print IsAtomic /-
/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
@[mk_iff]
class IsAtomic [OrderBot α] : Prop where
  eq_bot_or_exists_atom_le : ∀ b : α, b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b
#align is_atomic IsAtomic
-/

#print IsCoatomic /-
/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
@[mk_iff]
class IsCoatomic [OrderTop α] : Prop where
  eq_top_or_exists_le_coatom : ∀ b : α, b = ⊤ ∨ ∃ a : α, IsCoatom a ∧ b ≤ a
#align is_coatomic IsCoatomic
-/

export IsAtomic (eq_bot_or_exists_atom_le)

export IsCoatomic (eq_top_or_exists_le_coatom)

variable {α}

#print isCoatomic_dual_iff_isAtomic /-
@[simp]
theorem isCoatomic_dual_iff_isAtomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩, fun h =>
    ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩⟩
#align is_coatomic_dual_iff_is_atomic isCoatomic_dual_iff_isAtomic
-/

#print isAtomic_dual_iff_isCoatomic /-
@[simp]
theorem isAtomic_dual_iff_isCoatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩, fun h =>
    ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩⟩
#align is_atomic_dual_iff_is_coatomic isAtomic_dual_iff_isCoatomic
-/

namespace IsAtomic

variable [OrderBot α] [IsAtomic α]

#print IsAtomic.isCoatomic_dual /-
instance isCoatomic_dual : IsCoatomic αᵒᵈ :=
  isCoatomic_dual_iff_isAtomic.2 ‹IsAtomic α›
#align is_atomic.is_coatomic_dual IsAtomic.isCoatomic_dual
-/

instance {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.IicCat (hay.trans hy), hay⟩⟩

end IsAtomic

namespace IsCoatomic

variable [OrderTop α] [IsCoatomic α]

#print IsCoatomic.isCoatomic /-
instance isCoatomic : IsAtomic αᵒᵈ :=
  isAtomic_dual_iff_isCoatomic.2 ‹IsCoatomic α›
#align is_coatomic.is_coatomic IsCoatomic.isCoatomic
-/

instance {x : α} : IsCoatomic (Set.Ici x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_trans hy hay⟩, ha.IciCat (le_trans hy hay), hay⟩⟩

end IsCoatomic

#print isAtomic_iff_forall_isAtomic_Iic /-
theorem isAtomic_iff_forall_isAtomic_Iic [OrderBot α] :
    IsAtomic α ↔ ∀ x : α, IsAtomic (Set.Iic x) :=
  ⟨@IsAtomic.Set.Iic.isAtomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' coe fun ⟨a, ha⟩ => And.imp_left IsAtom.of_isAtom_coe_Iic)⟩⟩
#align is_atomic_iff_forall_is_atomic_Iic isAtomic_iff_forall_isAtomic_Iic
-/

#print isCoatomic_iff_forall_isCoatomic_Ici /-
theorem isCoatomic_iff_forall_isCoatomic_Ici [OrderTop α] :
    IsCoatomic α ↔ ∀ x : α, IsCoatomic (Set.Ici x) :=
  isAtomic_dual_iff_isCoatomic.symm.trans <|
    isAtomic_iff_forall_isAtomic_Iic.trans <|
      forall_congr' fun x => isCoatomic_dual_iff_isAtomic.symm.trans Iff.rfl
#align is_coatomic_iff_forall_is_coatomic_Ici isCoatomic_iff_forall_isCoatomic_Ici
-/

section WellFounded

#print isAtomic_of_orderBot_wellFounded_lt /-
theorem isAtomic_of_orderBot_wellFounded_lt [OrderBot α]
    (h : WellFounded ((· < ·) : α → α → Prop)) : IsAtomic α :=
  ⟨fun a =>
    or_iff_not_imp_left.2 fun ha =>
      let ⟨b, hb, hm⟩ := h.has_min { b | b ≠ ⊥ ∧ b ≤ a } ⟨a, ha, le_rfl⟩
      ⟨b, ⟨hb.1, fun c => not_imp_not.1 fun hc hl => hm c ⟨hc, hl.le.trans hb.2⟩ hl⟩, hb.2⟩⟩
#align is_atomic_of_order_bot_well_founded_lt isAtomic_of_orderBot_wellFounded_lt
-/

#print isCoatomic_of_orderTop_gt_wellFounded /-
theorem isCoatomic_of_orderTop_gt_wellFounded [OrderTop α]
    (h : WellFounded ((· > ·) : α → α → Prop)) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 (@isAtomic_of_orderBot_wellFounded_lt αᵒᵈ _ _ h)
#align is_coatomic_of_order_top_gt_well_founded isCoatomic_of_orderTop_gt_wellFounded
-/

end WellFounded

end Atomic

section Atomistic

variable (α) [CompleteLattice α]

#print IsAtomistic /-
/-- A lattice is atomistic iff every element is a `Sup` of a set of atoms. -/
class IsAtomistic : Prop where
  eq_Sup_atoms : ∀ b : α, ∃ s : Set α, b = supₛ s ∧ ∀ a, a ∈ s → IsAtom a
#align is_atomistic IsAtomistic
-/

#print IsCoatomistic /-
/-- A lattice is coatomistic iff every element is an `Inf` of a set of coatoms. -/
class IsCoatomistic : Prop where
  eq_Inf_coatoms : ∀ b : α, ∃ s : Set α, b = infₛ s ∧ ∀ a, a ∈ s → IsCoatom a
#align is_coatomistic IsCoatomistic
-/

export IsAtomistic (eq_Sup_atoms)

export IsCoatomistic (eq_Inf_coatoms)

variable {α}

#print isCoatomistic_dual_iff_isAtomistic /-
@[simp]
theorem isCoatomistic_dual_iff_isAtomistic : IsCoatomistic αᵒᵈ ↔ IsAtomistic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_Inf_coatoms⟩, fun h => ⟨fun b => by apply h.eq_Sup_atoms⟩⟩
#align is_coatomistic_dual_iff_is_atomistic isCoatomistic_dual_iff_isAtomistic
-/

#print isAtomistic_dual_iff_isCoatomistic /-
@[simp]
theorem isAtomistic_dual_iff_isCoatomistic : IsAtomistic αᵒᵈ ↔ IsCoatomistic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_Sup_atoms⟩, fun h => ⟨fun b => by apply h.eq_Inf_coatoms⟩⟩
#align is_atomistic_dual_iff_is_coatomistic isAtomistic_dual_iff_isCoatomistic
-/

namespace IsAtomistic

#print IsAtomistic.isCoatomistic_dual /-
instance isCoatomistic_dual [h : IsAtomistic α] : IsCoatomistic αᵒᵈ :=
  isCoatomistic_dual_iff_isAtomistic.2 h
#align is_atomistic.is_coatomistic_dual IsAtomistic.isCoatomistic_dual
-/

variable [IsAtomistic α]

instance (priority := 100) : IsAtomic α :=
  ⟨fun b => by
    rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩
    cases' s.eq_empty_or_nonempty with h h
    · simp [h]
    · exact Or.intro_right _ ⟨h.some, hs _ h.some_spec, le_supₛ h.some_spec⟩⟩

end IsAtomistic

section IsAtomistic

variable [IsAtomistic α]

/- warning: Sup_atoms_le_eq -> supₛ_atoms_le_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsAtomistic.{u1} α _inst_1] (b : α), Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => And (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b)))) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsAtomistic.{u1} α _inst_1] (b : α), Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (setOf.{u1} α (fun (a : α) => And (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b)))) b
Case conversion may be inaccurate. Consider using '#align Sup_atoms_le_eq supₛ_atoms_le_eqₓ'. -/
@[simp]
theorem supₛ_atoms_le_eq (b : α) : supₛ { a : α | IsAtom a ∧ a ≤ b } = b :=
  by
  rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩
  exact le_antisymm (supₛ_le fun _ => And.right) (supₛ_le_supₛ fun a ha => ⟨hs a ha, le_supₛ ha⟩)
#align Sup_atoms_le_eq supₛ_atoms_le_eq

/- warning: Sup_atoms_eq_top -> supₛ_atoms_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsAtomistic.{u1} α _inst_1], Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsAtomistic.{u1} α _inst_1], Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (setOf.{u1} α (fun (a : α) => IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Sup_atoms_eq_top supₛ_atoms_eq_topₓ'. -/
@[simp]
theorem supₛ_atoms_eq_top : supₛ { a : α | IsAtom a } = ⊤ :=
  by
  refine' Eq.trans (congr rfl (Set.ext fun x => _)) (supₛ_atoms_le_eq ⊤)
  exact (and_iff_left le_top).symm
#align Sup_atoms_eq_top supₛ_atoms_eq_top

#print le_iff_atom_le_imp /-
theorem le_iff_atom_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, IsAtom c → c ≤ a → c ≤ b :=
  ⟨fun ab c hc ca => le_trans ca ab, fun h =>
    by
    rw [← supₛ_atoms_le_eq a, ← supₛ_atoms_le_eq b]
    exact supₛ_le_supₛ fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩
#align le_iff_atom_le_imp le_iff_atom_le_imp
-/

end IsAtomistic

namespace IsCoatomistic

#print IsCoatomistic.isAtomistic_dual /-
instance isAtomistic_dual [h : IsCoatomistic α] : IsAtomistic αᵒᵈ :=
  isAtomistic_dual_iff_isCoatomistic.2 h
#align is_coatomistic.is_atomistic_dual IsCoatomistic.isAtomistic_dual
-/

variable [IsCoatomistic α]

instance (priority := 100) : IsCoatomic α :=
  ⟨fun b => by
    rcases eq_Inf_coatoms b with ⟨s, rfl, hs⟩
    cases' s.eq_empty_or_nonempty with h h
    · simp [h]
    · exact Or.intro_right _ ⟨h.some, hs _ h.some_spec, infₛ_le h.some_spec⟩⟩

end IsCoatomistic

end Atomistic

#print IsSimpleOrder /-
/-- An order is simple iff it has exactly two elements, `⊥` and `⊤`. -/
class IsSimpleOrder (α : Type _) [LE α] [BoundedOrder α] extends Nontrivial α : Prop where
  eq_bot_or_eq_top : ∀ a : α, a = ⊥ ∨ a = ⊤
#align is_simple_order IsSimpleOrder
-/

export IsSimpleOrder (eq_bot_or_eq_top)

#print isSimpleOrder_iff_isSimpleOrder_orderDual /-
theorem isSimpleOrder_iff_isSimpleOrder_orderDual [LE α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ :=
  by
  constructor <;> intro i <;> haveI := i
  ·
    exact
      { exists_pair_ne := @exists_pair_ne α _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.ofDual a) : _ ∨ _) }
  ·
    exact
      { exists_pair_ne := @exists_pair_ne αᵒᵈ _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.toDual a)) }
#align is_simple_order_iff_is_simple_order_order_dual isSimpleOrder_iff_isSimpleOrder_orderDual
-/

/- warning: is_simple_order.bot_ne_top -> IsSimpleOrder.bot_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : BoundedOrder.{u1} α _inst_1] [_inst_3 : IsSimpleOrder.{u1} α _inst_1 _inst_2], Ne.{succ u1} α (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α _inst_1 (BoundedOrder.toOrderBot.{u1} α _inst_1 _inst_2))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α _inst_1 (BoundedOrder.toOrderTop.{u1} α _inst_1 _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : BoundedOrder.{u1} α _inst_1] [_inst_3 : IsSimpleOrder.{u1} α _inst_1 _inst_2], Ne.{succ u1} α (Bot.bot.{u1} α (OrderBot.toBot.{u1} α _inst_1 (BoundedOrder.toOrderBot.{u1} α _inst_1 _inst_2))) (Top.top.{u1} α (OrderTop.toTop.{u1} α _inst_1 (BoundedOrder.toOrderTop.{u1} α _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align is_simple_order.bot_ne_top IsSimpleOrder.bot_ne_topₓ'. -/
theorem IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : α) ≠ (⊤ : α) :=
  by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first |simpa|simpa using h.symm
#align is_simple_order.bot_ne_top IsSimpleOrder.bot_ne_top

section IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

instance {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] : IsSimpleOrder αᵒᵈ :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.1 (by infer_instance)

#print IsSimpleOrder.preorder /-
/-- A simple `bounded_order` induces a preorder. This is not an instance to prevent loops. -/
protected def IsSimpleOrder.preorder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] : Preorder α
    where
  le := (· ≤ ·)
  le_refl a := by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans a b c := by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
      · simp
#align is_simple_order.preorder IsSimpleOrder.preorder
-/

#print IsSimpleOrder.linearOrder /-
/-- A simple partial ordered `bounded_order` induces a linear order.
This is not an instance to prevent loops. -/
protected def IsSimpleOrder.linearOrder [DecidableEq α] : LinearOrder α :=
  {
    (inferInstance :
      PartialOrder
        α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    decidableLe := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left (eq_bot_or_eq_top a) ha)) H))
    DecidableEq := by assumption }
#align is_simple_order.linear_order IsSimpleOrder.linearOrder
-/

/- warning: is_atom_top -> isAtom_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2], IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2], IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)))
Case conversion may be inaccurate. Consider using '#align is_atom_top isAtom_topₓ'. -/
@[simp]
theorem isAtom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩
#align is_atom_top isAtom_top

/- warning: is_coatom_bot -> isCoatom_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2], IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2], IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)))
Case conversion may be inaccurate. Consider using '#align is_coatom_bot isCoatom_botₓ'. -/
@[simp]
theorem isCoatom_bot : IsCoatom (⊥ : α) :=
  isAtom_dual_iff_isCoatom.1 isAtom_top
#align is_coatom_bot isCoatom_bot

/- warning: bot_covby_top -> bot_covby_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2], Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2], Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)))
Case conversion may be inaccurate. Consider using '#align bot_covby_top bot_covby_topₓ'. -/
theorem bot_covby_top : (⊥ : α) ⋖ ⊤ :=
  isAtom_top.bot_covby
#align bot_covby_top bot_covby_top

end IsSimpleOrder

namespace IsSimpleOrder

section Preorder

variable [Preorder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α} (h : a < b)

/- warning: is_simple_order.eq_bot_of_lt -> IsSimpleOrder.eq_bot_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Eq.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Eq.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_simple_order.eq_bot_of_lt IsSimpleOrder.eq_bot_of_ltₓ'. -/
theorem eq_bot_of_lt : a = ⊥ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top
#align is_simple_order.eq_bot_of_lt IsSimpleOrder.eq_bot_of_lt

/- warning: is_simple_order.eq_top_of_lt -> IsSimpleOrder.eq_top_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Eq.{succ u1} α b (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Eq.{succ u1} α b (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_simple_order.eq_top_of_lt IsSimpleOrder.eq_top_of_ltₓ'. -/
theorem eq_top_of_lt : b = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot
#align is_simple_order.eq_top_of_lt IsSimpleOrder.eq_top_of_lt

alias eq_bot_of_lt ← has_lt.lt.eq_bot

alias eq_top_of_lt ← has_lt.lt.eq_top

end Preorder

section BoundedOrder

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

#print IsSimpleOrder.lattice /-
/-- A simple partial ordered `bounded_order` induces a lattice.
This is not an instance to prevent loops -/
protected def lattice {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] :
    Lattice α :=
  @LinearOrder.toLattice α IsSimpleOrder.linearOrder
#align is_simple_order.lattice IsSimpleOrder.lattice
-/

#print IsSimpleOrder.distribLattice /-
/-- A lattice that is a `bounded_order` is a distributive lattice.
This is not an instance to prevent loops -/
protected def distribLattice : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
#align is_simple_order.distrib_lattice IsSimpleOrder.distribLattice
-/

-- see Note [lower instance priority]
instance (priority := 100) : IsAtomic α :=
  ⟨fun b => (eq_bot_or_eq_top b).imp_right fun h => ⟨⊤, ⟨isAtom_top, ge_of_eq h⟩⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 IsSimpleOrder.is_atomic

end BoundedOrder

-- It is important that in this section `is_simple_order` is the last type-class argument.
section DecidableEq

variable [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

#print IsSimpleOrder.equivBool /-
/-- Every simple lattice is isomorphic to `bool`, regardless of order. -/
@[simps]
def equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : α ≃ Bool
    where
  toFun x := x = ⊤
  invFun x := cond x ⊤ ⊥
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]
#align is_simple_order.equiv_bool IsSimpleOrder.equivBool
-/

/- warning: is_simple_order.order_iso_bool -> IsSimpleOrder.orderIsoBool is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3], OrderIso.{u1, 0} α Bool (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (GeneralizedCoheytingAlgebra.toLattice.{0} Bool (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{0} Bool (BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} Bool Bool.booleanAlgebra)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3], OrderIso.{u1, 0} α Bool (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (Preorder.toLE.{0} Bool (PartialOrder.toPreorder.{0} Bool (SemilatticeInf.toPartialOrder.{0} Bool (Lattice.toSemilatticeInf.{0} Bool (GeneralizedCoheytingAlgebra.toLattice.{0} Bool (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} Bool (BiheytingAlgebra.toCoheytingAlgebra.{0} Bool (BooleanAlgebra.toBiheytingAlgebra.{0} Bool instBooleanAlgebraBool))))))))
Case conversion may be inaccurate. Consider using '#align is_simple_order.order_iso_bool IsSimpleOrder.orderIsoBoolₓ'. -/
/-- Every simple lattice over a partial order is order-isomorphic to `bool`. -/
def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := fun a b =>
      by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp [bot_ne_top]
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, bot_ne_top, Bool.false_lt_true]
        · simp [bot_ne_top] }
#align is_simple_order.order_iso_bool IsSimpleOrder.orderIsoBool

#print IsSimpleOrder.booleanAlgebra /-
/-- A simple `bounded_order` is also a `boolean_algebra`. -/
protected def booleanAlgebra {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α] :
    BooleanAlgebra α :=
  { show BoundedOrder α by infer_instance,
    IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top, SDiff.sdiff, compl]
    inf_compl_le_bot := fun x =>
      by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp only [top_inf_eq]
        split_ifs with h h <;> simp [h]
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
#align is_simple_order.boolean_algebra IsSimpleOrder.booleanAlgebra
-/

end DecidableEq

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

open Classical

#print IsSimpleOrder.completeLattice /-
/-- A simple `bounded_order` is also complete. -/
protected noncomputable def completeLattice : CompleteLattice α :=
  { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder
        α) with
    sup := fun s => if ⊤ ∈ s then ⊤ else ⊥
    inf := fun s => if ⊥ ∈ s then ⊥ else ⊤
    le_Sup := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · rw [if_pos h]
    Sup_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · rw [if_neg]
        intro con
        exact bot_ne_top (eq_top_iff.2 (h ⊤ con))
      · exact le_top
    Inf_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · rw [if_pos h]
      · exact le_top
    le_Inf := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · rw [if_neg]
        intro con
        exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) }
#align is_simple_order.complete_lattice IsSimpleOrder.completeLattice
-/

#print IsSimpleOrder.completeBooleanAlgebra /-
/-- A simple `bounded_order` is also a `complete_boolean_algebra`. -/
protected noncomputable def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { IsSimpleOrder.completeLattice,
    IsSimpleOrder.booleanAlgebra with
    infi_sup_le_sup_Inf := fun x s =>
      by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [bot_sup_eq, ← infₛ_eq_infᵢ]
        exact le_rfl
      · simp only [top_sup_eq, le_top]
    inf_Sup_le_supr_inf := fun x s =>
      by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [bot_inf_eq, bot_le]
      · simp only [top_inf_eq, ← supₛ_eq_supᵢ]
        exact le_rfl }
#align is_simple_order.complete_boolean_algebra IsSimpleOrder.completeBooleanAlgebra
-/

end IsSimpleOrder

namespace IsSimpleOrder

variable [CompleteLattice α] [IsSimpleOrder α]

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option default_priority -/
set_option default_priority 100

instance : IsAtomistic α :=
  ⟨fun b =>
    (eq_bot_or_eq_top b).elim
      (fun h => ⟨∅, ⟨h.trans supₛ_empty.symm, fun a ha => False.elim (Set.not_mem_empty _ ha)⟩⟩)
      fun h =>
      ⟨{⊤}, h.trans supₛ_singleton.symm, fun a ha =>
        (Set.mem_singleton_iff.1 ha).symm ▸ isAtom_top⟩⟩

instance : IsCoatomistic α :=
  isAtomistic_dual_iff_isCoatomistic.1 IsSimpleOrder.is_atomistic

end IsSimpleOrder

/- warning: is_simple_order_iff_is_atom_top -> isSimpleOrder_iff_isAtom_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_simple_order_iff_is_atom_top isSimpleOrder_iff_isAtom_topₓ'. -/
theorem isSimpleOrder_iff_isAtom_top [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsAtom (⊤ : α) :=
  ⟨fun h => @isAtom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩
#align is_simple_order_iff_is_atom_top isSimpleOrder_iff_isAtom_top

/- warning: is_simple_order_iff_is_coatom_bot -> isSimpleOrder_iff_isCoatom_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_simple_order_iff_is_coatom_bot isSimpleOrder_iff_isCoatom_botₓ'. -/
theorem isSimpleOrder_iff_isCoatom_bot [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsCoatom (⊥ : α) :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.trans isSimpleOrder_iff_isAtom_top
#align is_simple_order_iff_is_coatom_bot isSimpleOrder_iff_isCoatom_bot

namespace Set

/- warning: set.is_simple_order_Iic_iff_is_atom -> Set.isSimpleOrder_Iic_iff_isAtom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, Iff (IsSimpleOrder.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a))) (Set.Iic.boundedOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] {a : α}, Iff (IsSimpleOrder.{u1} (Set.Elem.{u1} α (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a))) (Set.Iic.instBoundedOrderElemIicLeToLEMemSetInstMembershipSet.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)
Case conversion may be inaccurate. Consider using '#align set.is_simple_order_Iic_iff_is_atom Set.isSimpleOrder_Iic_iff_isAtomₓ'. -/
theorem isSimpleOrder_Iic_iff_isAtom [PartialOrder α] [OrderBot α] {a : α} :
    IsSimpleOrder (Iic a) ↔ IsAtom a :=
  isSimpleOrder_iff_isAtom_top.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, hab⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩
#align set.is_simple_order_Iic_iff_is_atom Set.isSimpleOrder_Iic_iff_isAtom

#print Set.isSimpleOrder_Ici_iff_isCoatom /-
theorem isSimpleOrder_Ici_iff_isCoatom [PartialOrder α] [OrderTop α] {a : α} :
    IsSimpleOrder (Ici a) ↔ IsCoatom a :=
  isSimpleOrder_iff_isCoatom_bot.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, hab⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩
#align set.is_simple_order_Ici_iff_is_coatom Set.isSimpleOrder_Ici_iff_isCoatom
-/

end Set

namespace OrderEmbedding

variable [PartialOrder α] [PartialOrder β]

/- warning: order_embedding.is_atom_of_map_bot_of_image -> OrderEmbedding.isAtom_of_map_bot_of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] (f : OrderEmbedding.{u2, u1} β α (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), (Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderEmbedding.{u2, u1} β α (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (fun (_x : RelEmbedding.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) => β -> α) (RelEmbedding.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) f (Bot.bot.{u2} β (OrderBot.toHasBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_4))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) -> (forall {b : β}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderEmbedding.{u2, u1} β α (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (fun (_x : RelEmbedding.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) => β -> α) (RelEmbedding.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) f b)) -> (IsAtom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] (f : OrderEmbedding.{u1, u2} β α (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))), (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (Bot.bot.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (OrderBot.toBot.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (Preorder.toLE.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (PartialOrder.toPreorder.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) _inst_1)) _inst_3))) -> (forall {b : β}, (IsAtom.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) b) (PartialOrder.toPreorder.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) b) _inst_1) _inst_3 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) b)) -> (IsAtom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 b))
Case conversion may be inaccurate. Consider using '#align order_embedding.is_atom_of_map_bot_of_image OrderEmbedding.isAtom_of_map_bot_of_imageₓ'. -/
theorem isAtom_of_map_bot_of_image [OrderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
    (hb : IsAtom (f b)) : IsAtom b :=
  by
  simp only [← bot_covby_iff] at hb⊢
  exact Covby.of_image f (hbot.symm ▸ hb)
#align order_embedding.is_atom_of_map_bot_of_image OrderEmbedding.isAtom_of_map_bot_of_image

/- warning: order_embedding.is_coatom_of_map_top_of_image -> OrderEmbedding.isCoatom_of_map_top_of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] (f : OrderEmbedding.{u2, u1} β α (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), (Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderEmbedding.{u2, u1} β α (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (fun (_x : RelEmbedding.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) => β -> α) (RelEmbedding.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) f (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_4))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) -> (forall {b : β}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderEmbedding.{u2, u1} β α (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (fun (_x : RelEmbedding.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) => β -> α) (RelEmbedding.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) f b)) -> (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] (f : OrderEmbedding.{u1, u2} β α (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))), (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (Top.top.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (OrderTop.toTop.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (Preorder.toLE.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (PartialOrder.toPreorder.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) _inst_1)) _inst_3))) -> (forall {b : β}, (IsCoatom.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) b) (PartialOrder.toPreorder.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) b) _inst_1) _inst_3 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) b)) -> (IsCoatom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 b))
Case conversion may be inaccurate. Consider using '#align order_embedding.is_coatom_of_map_top_of_image OrderEmbedding.isCoatom_of_map_top_of_imageₓ'. -/
theorem isCoatom_of_map_top_of_image [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤) {b : β}
    (hb : IsCoatom (f b)) : IsCoatom b :=
  f.dual.is_atom_of_map_bot_of_image htop hb
#align order_embedding.is_coatom_of_map_top_of_image OrderEmbedding.isCoatom_of_map_top_of_image

end OrderEmbedding

namespace GaloisInsertion

variable [PartialOrder α] [PartialOrder β]

/- warning: galois_insertion.is_atom_of_u_bot -> GaloisInsertion.isAtom_of_u_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (Eq.{succ u1} α (u (Bot.bot.{u2} β (OrderBot.toHasBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_4))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) -> (forall {b : β}, (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 (u b)) -> (IsAtom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (Eq.{succ u2} α (u (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) _inst_3))) -> (forall {b : β}, (IsAtom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (u b)) -> (IsAtom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 b))
Case conversion may be inaccurate. Consider using '#align galois_insertion.is_atom_of_u_bot GaloisInsertion.isAtom_of_u_botₓ'. -/
theorem isAtom_of_u_bot [OrderBot α] [OrderBot β] {l : α → β} {u : β → α} (gi : GaloisInsertion l u)
    (hbot : u ⊥ = ⊥) {b : β} (hb : IsAtom (u b)) : IsAtom b :=
  OrderEmbedding.isAtom_of_map_bot_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb
#align galois_insertion.is_atom_of_u_bot GaloisInsertion.isAtom_of_u_bot

/- warning: galois_insertion.is_atom_iff -> GaloisInsertion.isAtom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : IsAtomic.{u1} α _inst_1 _inst_3] [_inst_5 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (Eq.{succ u1} α (u (Bot.bot.{u2} β (OrderBot.toHasBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_5))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) -> (forall (a : α), (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a) -> (Eq.{succ u1} α (u (l a)) a)) -> (forall (a : α), Iff (IsAtom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_5 (l a)) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : IsAtomic.{u2} α _inst_1 _inst_3] [_inst_5 : OrderBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (Eq.{succ u2} α (u (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_5))) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) _inst_3))) -> (forall (a : α), (IsAtom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a) -> (Eq.{succ u2} α (u (l a)) a)) -> (forall (a : α), Iff (IsAtom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_5 (l a)) (IsAtom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a))
Case conversion may be inaccurate. Consider using '#align galois_insertion.is_atom_iff GaloisInsertion.isAtom_iffₓ'. -/
theorem isAtom_iff [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (a : α) :
    IsAtom (l a) ↔ IsAtom a :=
  by
  refine' ⟨fun hla => _, fun ha => gi.is_atom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩
  obtain ⟨a', ha', hab'⟩ :=
    (eq_bot_or_exists_atom_le (u (l a))).resolve_left (hbot ▸ fun h => hla.1 (gi.u_injective h))
  have :=
    (hla.le_iff.mp <| (gi.l_u_eq (l a) ▸ gi.gc.monotone_l hab' : l a' ≤ l a)).resolve_left fun h =>
      ha'.1 (hbot ▸ h_atom a' ha' ▸ congr_arg u h)
  have haa' : a = a' :=
    (ha'.le_iff.mp <|
          (gi.gc.le_u_l a).trans_eq (h_atom a' ha' ▸ congr_arg u this.symm)).resolve_left
      (mt (congr_arg l) (gi.gc.l_bot.symm ▸ hla.1))
  exact haa'.symm ▸ ha'
#align galois_insertion.is_atom_iff GaloisInsertion.isAtom_iff

/- warning: galois_insertion.is_atom_iff' -> GaloisInsertion.isAtom_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : IsAtomic.{u1} α _inst_1 _inst_3] [_inst_5 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (Eq.{succ u1} α (u (Bot.bot.{u2} β (OrderBot.toHasBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_5))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) -> (forall (a : α), (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a) -> (Eq.{succ u1} α (u (l a)) a)) -> (forall (b : β), Iff (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 (u b)) (IsAtom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_5 b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : IsAtomic.{u2} α _inst_1 _inst_3] [_inst_5 : OrderBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (Eq.{succ u2} α (u (Bot.bot.{u1} β (OrderBot.toBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_5))) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) _inst_3))) -> (forall (a : α), (IsAtom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a) -> (Eq.{succ u2} α (u (l a)) a)) -> (forall (b : β), Iff (IsAtom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (u b)) (IsAtom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_5 b))
Case conversion may be inaccurate. Consider using '#align galois_insertion.is_atom_iff' GaloisInsertion.isAtom_iff'ₓ'. -/
theorem isAtom_iff' [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (b : β) :
    IsAtom (u b) ↔ IsAtom b := by rw [← gi.is_atom_iff hbot h_atom, gi.l_u_eq]
#align galois_insertion.is_atom_iff' GaloisInsertion.isAtom_iff'

/- warning: galois_insertion.is_coatom_of_image -> GaloisInsertion.isCoatom_of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (forall {b : β}, (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 (u b)) -> (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (forall {b : β}, (IsCoatom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (u b)) -> (IsCoatom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 b))
Case conversion may be inaccurate. Consider using '#align galois_insertion.is_coatom_of_image GaloisInsertion.isCoatom_of_imageₓ'. -/
theorem isCoatom_of_image [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) {b : β} (hb : IsCoatom (u b)) : IsCoatom b :=
  OrderEmbedding.isCoatom_of_map_top_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb
#align galois_insertion.is_coatom_of_image GaloisInsertion.isCoatom_of_image

/- warning: galois_insertion.is_coatom_iff -> GaloisInsertion.isCoatom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : IsCoatomic.{u1} α _inst_1 _inst_3] [_inst_5 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (forall (a : α), (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a) -> (Eq.{succ u1} α (u (l a)) a)) -> (forall (b : β), Iff (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 (u b)) (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_5 b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : IsCoatomic.{u2} α _inst_1 _inst_3] [_inst_5 : OrderTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisInsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (forall (a : α), (IsCoatom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a) -> (Eq.{succ u2} α (u (l a)) a)) -> (forall (b : β), Iff (IsCoatom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (u b)) (IsCoatom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_5 b))
Case conversion may be inaccurate. Consider using '#align galois_insertion.is_coatom_iff GaloisInsertion.isCoatom_iffₓ'. -/
theorem isCoatom_iff [OrderTop α] [IsCoatomic α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (h_coatom : ∀ a : α, IsCoatom a → u (l a) = a) (b : β) :
    IsCoatom (u b) ↔ IsCoatom b :=
  by
  refine' ⟨fun hb => gi.is_coatom_of_image hb, fun hb => _⟩
  obtain ⟨a, ha, hab⟩ :=
    (eq_top_or_exists_le_coatom (u b)).resolve_left fun h =>
      hb.1 <| (gi.gc.u_top ▸ gi.l_u_eq ⊤ : l ⊤ = ⊤) ▸ gi.l_u_eq b ▸ congr_arg l h
  have : l a = b :=
    (hb.le_iff.mp (gi.l_u_eq b ▸ gi.gc.monotone_l hab : b ≤ l a)).resolve_left fun hla =>
      ha.1 (gi.gc.u_top ▸ h_coatom a ha ▸ congr_arg u hla)
  exact this ▸ (h_coatom a ha).symm ▸ ha
#align galois_insertion.is_coatom_iff GaloisInsertion.isCoatom_iff

end GaloisInsertion

namespace GaloisCoinsertion

variable [PartialOrder α] [PartialOrder β]

/- warning: galois_coinsertion.is_coatom_of_l_top -> GaloisCoinsertion.isCoatom_of_l_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (Eq.{succ u2} β (l (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_4))) -> (forall {a : α}, (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 (l a)) -> (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (Eq.{succ u1} β (l (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) _inst_3))) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) -> (forall {a : α}, (IsCoatom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 (l a)) -> (IsCoatom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a))
Case conversion may be inaccurate. Consider using '#align galois_coinsertion.is_coatom_of_l_top GaloisCoinsertion.isCoatom_of_l_topₓ'. -/
theorem isCoatom_of_l_top [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (hbot : l ⊤ = ⊤) {a : α} (hb : IsCoatom (l a)) : IsCoatom a :=
  gi.dual.is_atom_of_u_bot hbot hb.dual
#align galois_coinsertion.is_coatom_of_l_top GaloisCoinsertion.isCoatom_of_l_top

/- warning: galois_coinsertion.is_coatom_iff -> GaloisCoinsertion.isCoatom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] [_inst_5 : IsCoatomic.{u2} β _inst_2 _inst_4] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (Eq.{succ u2} β (l (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_4))) -> (forall (b : β), (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 b) -> (Eq.{succ u2} β (l (u b)) b)) -> (forall (b : β), Iff (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 (u b)) (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] [_inst_5 : IsCoatomic.{u1} β _inst_2 _inst_4] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (Eq.{succ u1} β (l (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) _inst_3))) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) -> (forall (b : β), (IsCoatom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 b) -> (Eq.{succ u1} β (l (u b)) b)) -> (forall (b : β), Iff (IsCoatom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (u b)) (IsCoatom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 b))
Case conversion may be inaccurate. Consider using '#align galois_coinsertion.is_coatom_iff GaloisCoinsertion.isCoatom_iffₓ'. -/
theorem isCoatom_iff [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (b : β) : IsCoatom (u b) ↔ IsCoatom b :=
  gi.dual.is_atom_iff htop h_coatom b
#align galois_coinsertion.is_coatom_iff GaloisCoinsertion.isCoatom_iff

/- warning: galois_coinsertion.is_coatom_iff' -> GaloisCoinsertion.isCoatom_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] [_inst_5 : IsCoatomic.{u2} β _inst_2 _inst_4] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (Eq.{succ u2} β (l (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_4))) -> (forall (b : β), (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 b) -> (Eq.{succ u2} β (l (u b)) b)) -> (forall (a : α), Iff (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 (l a)) (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] [_inst_5 : IsCoatomic.{u1} β _inst_2 _inst_4] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (Eq.{succ u1} β (l (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) _inst_3))) (Top.top.{u1} β (OrderTop.toTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))) -> (forall (b : β), (IsCoatom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 b) -> (Eq.{succ u1} β (l (u b)) b)) -> (forall (a : α), Iff (IsCoatom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 (l a)) (IsCoatom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a))
Case conversion may be inaccurate. Consider using '#align galois_coinsertion.is_coatom_iff' GaloisCoinsertion.isCoatom_iff'ₓ'. -/
theorem isCoatom_iff' [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (a : α) : IsCoatom (l a) ↔ IsCoatom a :=
  gi.dual.is_atom_iff' htop h_coatom a
#align galois_coinsertion.is_coatom_iff' GaloisCoinsertion.isCoatom_iff'

/- warning: galois_coinsertion.is_atom_of_image -> GaloisCoinsertion.isAtom_of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (forall {a : α}, (IsAtom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 (l a)) -> (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (forall {a : α}, (IsAtom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 (l a)) -> (IsAtom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a))
Case conversion may be inaccurate. Consider using '#align galois_coinsertion.is_atom_of_image GaloisCoinsertion.isAtom_of_imageₓ'. -/
theorem isAtom_of_image [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) {a : α} (hb : IsAtom (l a)) : IsAtom a :=
  gi.dual.is_coatom_of_image hb.dual
#align galois_coinsertion.is_atom_of_image GaloisCoinsertion.isAtom_of_image

/- warning: galois_coinsertion.is_atom_iff -> GaloisCoinsertion.isAtom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] [_inst_5 : IsAtomic.{u2} β _inst_2 _inst_4] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) l u) -> (forall (b : β), (IsAtom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 b) -> (Eq.{succ u2} β (l (u b)) b)) -> (forall (a : α), Iff (IsAtom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 (l a)) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] [_inst_5 : IsAtomic.{u1} β _inst_2 _inst_4] {l : α -> β} {u : β -> α}, (GaloisCoinsertion.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) l u) -> (forall (b : β), (IsAtom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 b) -> (Eq.{succ u1} β (l (u b)) b)) -> (forall (a : α), Iff (IsAtom.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) _inst_4 (l a)) (IsAtom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a))
Case conversion may be inaccurate. Consider using '#align galois_coinsertion.is_atom_iff GaloisCoinsertion.isAtom_iffₓ'. -/
theorem isAtom_iff [OrderBot α] [OrderBot β] [IsAtomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (h_atom : ∀ b, IsAtom b → l (u b) = b) (a : α) :
    IsAtom (l a) ↔ IsAtom a :=
  gi.dual.is_coatom_iff h_atom a
#align galois_coinsertion.is_atom_iff GaloisCoinsertion.isAtom_iff

end GaloisCoinsertion

namespace OrderIso

variable [PartialOrder α] [PartialOrder β]

/- warning: order_iso.is_atom_iff -> OrderIso.isAtom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (a : α), Iff (IsAtom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)))) f a)) (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] (f : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))) (a : α), Iff (IsAtom.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) _inst_2) _inst_4 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) f)) a)) (IsAtom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a)
Case conversion may be inaccurate. Consider using '#align order_iso.is_atom_iff OrderIso.isAtom_iffₓ'. -/
@[simp]
theorem isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (a : α) : IsAtom (f a) ↔ IsAtom a :=
  ⟨f.toGaloisCoinsertion.is_atom_of_image, fun ha =>
    f.toGaloisInsertion.is_atom_of_u_bot (map_bot f.symm) <| (f.symm_apply_apply a).symm ▸ ha⟩
#align order_iso.is_atom_iff OrderIso.isAtom_iff

/- warning: order_iso.is_coatom_iff -> OrderIso.isCoatom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (a : α), Iff (IsCoatom.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) _inst_4 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)))) f a)) (IsCoatom.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] (f : OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))) (a : α), Iff (IsCoatom.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) _inst_2) _inst_4 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) f)) a)) (IsCoatom.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 a)
Case conversion may be inaccurate. Consider using '#align order_iso.is_coatom_iff OrderIso.isCoatom_iffₓ'. -/
@[simp]
theorem isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o β) (a : α) : IsCoatom (f a) ↔ IsCoatom a :=
  f.dual.is_atom_iff a
#align order_iso.is_coatom_iff OrderIso.isCoatom_iff

/- warning: order_iso.is_simple_order_iff -> OrderIso.isSimpleOrder_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : BoundedOrder.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))], (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) -> (Iff (IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3) (IsSimpleOrder.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_4))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : BoundedOrder.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : BoundedOrder.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))], (OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))) -> (Iff (IsSimpleOrder.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) _inst_3) (IsSimpleOrder.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4))
Case conversion may be inaccurate. Consider using '#align order_iso.is_simple_order_iff OrderIso.isSimpleOrder_iffₓ'. -/
theorem isSimpleOrder_iff [BoundedOrder α] [BoundedOrder β] (f : α ≃o β) :
    IsSimpleOrder α ↔ IsSimpleOrder β := by
  rw [isSimpleOrder_iff_isAtom_top, isSimpleOrder_iff_isAtom_top, ← f.is_atom_iff ⊤, f.map_top]
#align order_iso.is_simple_order_iff OrderIso.isSimpleOrder_iff

/- warning: order_iso.is_simple_order -> OrderIso.isSimpleOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : BoundedOrder.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))] [h : IsSimpleOrder.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) _inst_4], (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) -> (IsSimpleOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : BoundedOrder.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : BoundedOrder.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))] [h : IsSimpleOrder.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) _inst_4], (OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))) -> (IsSimpleOrder.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) _inst_3)
Case conversion may be inaccurate. Consider using '#align order_iso.is_simple_order OrderIso.isSimpleOrderₓ'. -/
theorem isSimpleOrder [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f : α ≃o β) :
    IsSimpleOrder α :=
  f.is_simple_order_iff.mpr h
#align order_iso.is_simple_order OrderIso.isSimpleOrder

/- warning: order_iso.is_atomic_iff -> OrderIso.isAtomic_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))], (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) -> (Iff (IsAtomic.{u1} α _inst_1 _inst_3) (IsAtomic.{u2} β _inst_2 _inst_4))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderBot.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))], (OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))) -> (Iff (IsAtomic.{u2} α _inst_1 _inst_3) (IsAtomic.{u1} β _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align order_iso.is_atomic_iff OrderIso.isAtomic_iffₓ'. -/
protected theorem isAtomic_iff [OrderBot α] [OrderBot β] (f : α ≃o β) : IsAtomic α ↔ IsAtomic β :=
  by
  simp only [is_atomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.is_atom_iff]
#align order_iso.is_atomic_iff OrderIso.isAtomic_iff

/- warning: order_iso.is_coatomic_iff -> OrderIso.isCoatomic_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : OrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))], (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) -> (Iff (IsCoatomic.{u1} α _inst_1 _inst_3) (IsCoatomic.{u2} β _inst_2 _inst_4))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] [_inst_3 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))] [_inst_4 : OrderTop.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))], (OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))) -> (Iff (IsCoatomic.{u2} α _inst_1 _inst_3) (IsCoatomic.{u1} β _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align order_iso.is_coatomic_iff OrderIso.isCoatomic_iffₓ'. -/
protected theorem isCoatomic_iff [OrderTop α] [OrderTop β] (f : α ≃o β) :
    IsCoatomic α ↔ IsCoatomic β := by
  simp only [← isAtomic_dual_iff_isCoatomic, f.dual.is_atomic_iff]
#align order_iso.is_coatomic_iff OrderIso.isCoatomic_iff

end OrderIso

section IsModularLattice

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

namespace IsCompl

variable {a b : α} (hc : IsCompl a b)

include hc

#print IsCompl.isAtom_iff_isCoatom /-
theorem isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b :=
  Set.isSimpleOrder_Iic_iff_isAtom.symm.trans <|
    hc.IicOrderIsoIci.is_simple_order_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom
#align is_compl.is_atom_iff_is_coatom IsCompl.isAtom_iff_isCoatom
-/

#print IsCompl.isCoatom_iff_isAtom /-
theorem isCoatom_iff_isAtom : IsCoatom a ↔ IsAtom b :=
  hc.symm.is_atom_iff_is_coatom.symm
#align is_compl.is_coatom_iff_is_atom IsCompl.isCoatom_iff_isAtom
-/

end IsCompl

variable [ComplementedLattice α]

#print isCoatomic_of_isAtomic_of_complementedLattice_of_isModular /-
theorem isCoatomic_of_isAtomic_of_complementedLattice_of_isModular [IsAtomic α] : IsCoatomic α :=
  ⟨fun x => by
    rcases exists_is_compl x with ⟨y, xy⟩
    apply (eq_bot_or_exists_atom_le y).imp _ _
    · rintro rfl
      exact eq_top_of_isCompl_bot xy
    · rintro ⟨a, ha, ay⟩
      rcases exists_is_compl (xy.symm.Iic_order_iso_Ici ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
      refine' ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_isCoatom_coe_Ici _, xb⟩
      rw [← hb.is_atom_iff_is_coatom, OrderIso.isAtom_iff]
      apply ha.Iic⟩
#align
  is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular isCoatomic_of_isAtomic_of_complementedLattice_of_isModular
-/

#print isAtomic_of_isCoatomic_of_complementedLattice_of_isModular /-
theorem isAtomic_of_isCoatomic_of_complementedLattice_of_isModular [IsCoatomic α] : IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.1 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular
#align
  is_atomic_of_is_coatomic_of_complemented_lattice_of_is_modular isAtomic_of_isCoatomic_of_complementedLattice_of_isModular
-/

#print isAtomic_iff_isCoatomic /-
theorem isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun h => @isCoatomic_of_isAtomic_of_complementedLattice_of_isModular _ _ _ _ _ h, fun h =>
    @isAtomic_of_isCoatomic_of_complementedLattice_of_isModular _ _ _ _ _ h⟩
#align is_atomic_iff_is_coatomic isAtomic_iff_isCoatomic
-/

end IsModularLattice

namespace Set

/- warning: set.is_atom_singleton -> Set.isAtom_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α), IsAtom.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)
but is expected to have type
  forall {α : Type.{u1}} (x : α), IsAtom.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)
Case conversion may be inaccurate. Consider using '#align set.is_atom_singleton Set.isAtom_singletonₓ'. -/
theorem isAtom_singleton (x : α) : IsAtom ({x} : Set α) :=
  ⟨singleton_ne_empty _, fun s hs => ssubset_singleton_iff.mp hs⟩
#align set.is_atom_singleton Set.isAtom_singleton

/- warning: set.is_atom_iff -> Set.isAtom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Iff (IsAtom.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s) (Exists.{succ u1} α (fun (x : α) => Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Iff (IsAtom.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s) (Exists.{succ u1} α (fun (x : α) => Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align set.is_atom_iff Set.isAtom_iffₓ'. -/
theorem isAtom_iff (s : Set α) : IsAtom s ↔ ∃ x, s = {x} :=
  by
  refine'
    ⟨_, by
      rintro ⟨x, rfl⟩
      exact is_atom_singleton x⟩
  rw [isAtom_iff, bot_eq_empty, ← nonempty_iff_ne_empty]
  rintro ⟨⟨x, hx⟩, hs⟩
  exact
    ⟨x,
      eq_singleton_iff_unique_mem.2
        ⟨hx, fun y hy => (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩
#align set.is_atom_iff Set.isAtom_iff

/- warning: set.is_coatom_iff -> Set.isCoatom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Iff (IsCoatom.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Set.orderTop.{u1} α) s) (Exists.{succ u1} α (fun (x : α) => Eq.{succ u1} (Set.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Iff (IsCoatom.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.instOrderTopSetInstLESet.{u1} α) s) (Exists.{succ u1} α (fun (x : α) => Eq.{succ u1} (Set.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))))
Case conversion may be inaccurate. Consider using '#align set.is_coatom_iff Set.isCoatom_iffₓ'. -/
theorem isCoatom_iff (s : Set α) : IsCoatom s ↔ ∃ x, s = {x}ᶜ := by
  simp_rw [is_compl_compl.is_coatom_iff_is_atom, isAtom_iff, @eq_comm _ s, compl_eq_comm]
#align set.is_coatom_iff Set.isCoatom_iff

/- warning: set.is_coatom_singleton_compl -> Set.isCoatom_singleton_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α), IsCoatom.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Set.orderTop.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} (x : α), IsCoatom.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.instOrderTopSetInstLESet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align set.is_coatom_singleton_compl Set.isCoatom_singleton_complₓ'. -/
theorem isCoatom_singleton_compl (x : α) : IsCoatom ({x}ᶜ : Set α) :=
  (isCoatom_iff ({x}ᶜ)).mpr ⟨x, rfl⟩
#align set.is_coatom_singleton_compl Set.isCoatom_singleton_compl

instance : IsAtomistic (Set α)
    where eq_Sup_atoms s :=
    ⟨(fun x => {x}) '' s, by rw [Sup_eq_sUnion, sUnion_image, bUnion_of_singleton],
      by
      rintro - ⟨x, hx, rfl⟩
      exact is_atom_singleton x⟩

instance : IsCoatomistic (Set α)
    where eq_Inf_coatoms s :=
    ⟨(fun x => {x}ᶜ) '' sᶜ, by
      rw [Inf_eq_sInter, sInter_image, ← compl_Union₂, bUnion_of_singleton, compl_compl],
      by
      rintro - ⟨x, hx, rfl⟩
      exact is_coatom_singleton_compl x⟩

end Set

