/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.prop_instances
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Disjoint
import Mathbin.Order.WithBot

/-!

# The order on `Prop`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/792
> Any changes to this file require a corresponding PR to mathlib4.

Instances on `Prop` such as `distrib_lattice`, `bounded_order`, `linear_order`.

-/


#print Prop.distribLattice /-
/-- Propositions form a distributive lattice. -/
instance Prop.distribLattice : DistribLattice Prop :=
  { PropCat.partialOrder with 
    sup := Or
    le_sup_left := @Or.inl
    le_sup_right := @Or.inr
    sup_le := fun a b c => Or.ndrec
    inf := And
    inf_le_left := @And.left
    inf_le_right := @And.right
    le_inf := fun a b c Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
    le_sup_inf := fun a b c => or_and_left.2 }
#align Prop.distrib_lattice Prop.distribLattice
-/

#print Prop.boundedOrder /-
/-- Propositions form a bounded order. -/
instance Prop.boundedOrder : BoundedOrder
      Prop where 
  top := True
  le_top a Ha := True.intro
  bot := False
  bot_le := @False.elim
#align Prop.bounded_order Prop.boundedOrder
-/

/- warning: Prop.bot_eq_false -> Prop.bot_eq_false is a dubious translation:
lean 3 declaration is
  Eq.{1} Prop (Bot.bot.{0} Prop (OrderBot.toHasBot.{0} Prop PropCat.hasLe (BoundedOrder.toOrderBot.{0} Prop PropCat.hasLe Prop.boundedOrder))) False
but is expected to have type
  Eq.{1} Prop (Bot.bot.{0} Prop (OrderBot.toBot.{0} Prop instLEProp (BoundedOrder.toOrderBot.{0} Prop instLEProp Prop.boundedOrder))) False
Case conversion may be inaccurate. Consider using '#align Prop.bot_eq_false Prop.bot_eq_falseₓ'. -/
theorem Prop.bot_eq_false : (⊥ : Prop) = False :=
  rfl
#align Prop.bot_eq_false Prop.bot_eq_false

/- warning: Prop.top_eq_true -> Prop.top_eq_true is a dubious translation:
lean 3 declaration is
  Eq.{1} Prop (Top.top.{0} Prop (OrderTop.toHasTop.{0} Prop PropCat.hasLe (BoundedOrder.toOrderTop.{0} Prop PropCat.hasLe Prop.boundedOrder))) True
but is expected to have type
  Eq.{1} Prop (Top.top.{0} Prop (OrderTop.toTop.{0} Prop instLEProp (BoundedOrder.toOrderTop.{0} Prop instLEProp Prop.boundedOrder))) True
Case conversion may be inaccurate. Consider using '#align Prop.top_eq_true Prop.top_eq_trueₓ'. -/
theorem Prop.top_eq_true : (⊤ : Prop) = True :=
  rfl
#align Prop.top_eq_true Prop.top_eq_true

#print Prop.le_is_total /-
instance Prop.le_is_total : IsTotal Prop (· ≤ ·) :=
  ⟨fun p q => by 
    change (p → q) ∨ (q → p)
    tauto!⟩
#align Prop.le_is_total Prop.le_is_total
-/

#print Prop.linearOrder /-
noncomputable instance Prop.linearOrder : LinearOrder Prop := by
  classical exact Lattice.toLinearOrder Prop
#align Prop.linear_order Prop.linearOrder
-/

#print sup_Prop_eq /-
@[simp]
theorem sup_Prop_eq : (· ⊔ ·) = (· ∨ ·) :=
  rfl
#align sup_Prop_eq sup_Prop_eq
-/

#print inf_Prop_eq /-
@[simp]
theorem inf_Prop_eq : (· ⊓ ·) = (· ∧ ·) :=
  rfl
#align inf_Prop_eq inf_Prop_eq
-/

namespace Pi

variable {ι : Type _} {α' : ι → Type _} [∀ i, PartialOrder (α' i)]

/- warning: pi.disjoint_iff -> Pi.disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), OrderBot.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (Disjoint.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.orderBot.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => (fun (i : ι) => α' i) i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), Disjoint.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
but is expected to have type
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), OrderBot.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (Disjoint.{max u1 u2} (forall (i : ι), α' i) (instPartialOrderForAll.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.orderBot.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => α' i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), Disjoint.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align pi.disjoint_iff Pi.disjoint_iffₓ'. -/
theorem disjoint_iff [∀ i, OrderBot (α' i)] {f g : ∀ i, α' i} :
    Disjoint f g ↔ ∀ i, Disjoint (f i) (g i) := by
  constructor
  · intro h i x hf hg
    refine'
      (update_le_iff.mp <|-- this line doesn't work
            h
            (update_le_iff.mpr ⟨hf, fun _ _ => _⟩) (update_le_iff.mpr ⟨hg, fun _ _ => _⟩)).1
    · exact ⊥
    · exact bot_le
    · exact bot_le
  · intro h x hf hg i
    apply h i (hf i) (hg i)
#align pi.disjoint_iff Pi.disjoint_iff

/- warning: pi.codisjoint_iff -> Pi.codisjoint_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), OrderTop.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (Codisjoint.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.orderTop.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => (fun (i : ι) => α' i) i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), Codisjoint.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
but is expected to have type
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), OrderTop.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (Codisjoint.{max u1 u2} (forall (i : ι), α' i) (instPartialOrderForAll.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.orderTop.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => α' i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), Codisjoint.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align pi.codisjoint_iff Pi.codisjoint_iffₓ'. -/
theorem codisjoint_iff [∀ i, OrderTop (α' i)] {f g : ∀ i, α' i} :
    Codisjoint f g ↔ ∀ i, Codisjoint (f i) (g i) :=
  @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _
#align pi.codisjoint_iff Pi.codisjoint_iff

/- warning: pi.is_compl_iff -> Pi.isCompl_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), BoundedOrder.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (IsCompl.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.boundedOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => (fun (i : ι) => α' i) i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), IsCompl.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
but is expected to have type
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), BoundedOrder.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (IsCompl.{max u1 u2} (forall (i : ι), α' i) (instPartialOrderForAll.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.boundedOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => α' i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), IsCompl.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align pi.is_compl_iff Pi.isCompl_iffₓ'. -/
theorem isCompl_iff [∀ i, BoundedOrder (α' i)] {f g : ∀ i, α' i} :
    IsCompl f g ↔ ∀ i, IsCompl (f i) (g i) := by
  simp_rw [isCompl_iff, disjoint_iff, codisjoint_iff, forall_and]
#align pi.is_compl_iff Pi.isCompl_iff

end Pi

/- warning: Prop.disjoint_iff -> Prop.disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {P : Prop} {Q : Prop}, Iff (Disjoint.{0} Prop PropCat.partialOrder (BoundedOrder.toOrderBot.{0} Prop (Preorder.toLE.{0} Prop (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder)) Prop.boundedOrder) P Q) (Not (And P Q))
but is expected to have type
  forall {P : Prop} {Q : Prop}, Iff (Disjoint.{0} Prop instPartialOrderProp (BoundedOrder.toOrderBot.{0} Prop (Preorder.toLE.{0} Prop (PartialOrder.toPreorder.{0} Prop instPartialOrderProp)) Prop.boundedOrder) P Q) (Not (And P Q))
Case conversion may be inaccurate. Consider using '#align Prop.disjoint_iff Prop.disjoint_iffₓ'. -/
@[simp]
theorem Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q) :=
  disjoint_iff_inf_le
#align Prop.disjoint_iff Prop.disjoint_iff

/- warning: Prop.codisjoint_iff -> Prop.codisjoint_iff is a dubious translation:
lean 3 declaration is
  forall {P : Prop} {Q : Prop}, Iff (Codisjoint.{0} Prop PropCat.partialOrder (BoundedOrder.toOrderTop.{0} Prop (Preorder.toLE.{0} Prop (PartialOrder.toPreorder.{0} Prop PropCat.partialOrder)) Prop.boundedOrder) P Q) (Or P Q)
but is expected to have type
  forall {P : Prop} {Q : Prop}, Iff (Codisjoint.{0} Prop instPartialOrderProp (BoundedOrder.toOrderTop.{0} Prop (Preorder.toLE.{0} Prop (PartialOrder.toPreorder.{0} Prop instPartialOrderProp)) Prop.boundedOrder) P Q) (Or P Q)
Case conversion may be inaccurate. Consider using '#align Prop.codisjoint_iff Prop.codisjoint_iffₓ'. -/
@[simp]
theorem Prop.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q :=
  codisjoint_iff_le_sup.trans <| forall_const _
#align Prop.codisjoint_iff Prop.codisjoint_iff

/- warning: Prop.is_compl_iff -> Prop.isCompl_iff is a dubious translation:
lean 3 declaration is
  forall {P : Prop} {Q : Prop}, Iff (IsCompl.{0} Prop PropCat.partialOrder Prop.boundedOrder P Q) (Not (Iff P Q))
but is expected to have type
  forall {P : Prop} {Q : Prop}, Iff (IsCompl.{0} Prop instPartialOrderProp Prop.boundedOrder P Q) (Not (Iff P Q))
Case conversion may be inaccurate. Consider using '#align Prop.is_compl_iff Prop.isCompl_iffₓ'. -/
@[simp]
theorem Prop.isCompl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q) := by
  rw [isCompl_iff, Prop.disjoint_iff, Prop.codisjoint_iff, not_iff]
  tauto
#align Prop.is_compl_iff Prop.isCompl_iff

