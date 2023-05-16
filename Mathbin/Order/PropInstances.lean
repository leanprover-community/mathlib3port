/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.prop_instances
! leanprover-community/mathlib commit 6623e6af705e97002a9054c1c05a980180276fc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Disjoint
import Mathbin.Order.WithBot

/-!

# The order on `Prop`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Instances on `Prop` such as `distrib_lattice`, `bounded_order`, `linear_order`.

-/


#print Prop.distribLattice /-
/-- Propositions form a distributive lattice. -/
instance Prop.distribLattice : DistribLattice Prop :=
  { Prop.partialOrder with
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
instance Prop.boundedOrder : BoundedOrder Prop
    where
  top := True
  le_top a Ha := True.intro
  bot := False
  bot_le := @False.elim
#align Prop.bounded_order Prop.boundedOrder
-/

/- warning: Prop.bot_eq_false -> Prop.bot_eq_false is a dubious translation:
lean 3 declaration is
  Eq.{1} Prop (Bot.bot.{0} Prop (OrderBot.toHasBot.{0} Prop Prop.le (BoundedOrder.toOrderBot.{0} Prop Prop.le Prop.boundedOrder))) False
but is expected to have type
  Eq.{1} Prop (Bot.bot.{0} Prop (OrderBot.toBot.{0} Prop Prop.le (BoundedOrder.toOrderBot.{0} Prop Prop.le Prop.boundedOrder))) False
Case conversion may be inaccurate. Consider using '#align Prop.bot_eq_false Prop.bot_eq_falseₓ'. -/
theorem Prop.bot_eq_false : (⊥ : Prop) = False :=
  rfl
#align Prop.bot_eq_false Prop.bot_eq_false

/- warning: Prop.top_eq_true -> Prop.top_eq_true is a dubious translation:
lean 3 declaration is
  Eq.{1} Prop (Top.top.{0} Prop (OrderTop.toHasTop.{0} Prop Prop.le (BoundedOrder.toOrderTop.{0} Prop Prop.le Prop.boundedOrder))) True
but is expected to have type
  Eq.{1} Prop (Top.top.{0} Prop (OrderTop.toTop.{0} Prop Prop.le (BoundedOrder.toOrderTop.{0} Prop Prop.le Prop.boundedOrder))) True
Case conversion may be inaccurate. Consider using '#align Prop.top_eq_true Prop.top_eq_trueₓ'. -/
theorem Prop.top_eq_true : (⊤ : Prop) = True :=
  rfl
#align Prop.top_eq_true Prop.top_eq_true

#print Prop.le_isTotal /-
instance Prop.le_isTotal : IsTotal Prop (· ≤ ·) :=
  ⟨fun p q => by
    change (p → q) ∨ (q → p)
    tauto⟩
#align Prop.le_is_total Prop.le_isTotal
-/

#print Prop.linearOrder /-
noncomputable instance Prop.linearOrder : LinearOrder Prop := by
  classical exact Lattice.toLinearOrder Prop
#align Prop.linear_order Prop.linearOrder
-/

/- warning: sup_Prop_eq -> sup_Prop_eq is a dubious translation:
lean 3 declaration is
  Eq.{1} (Prop -> Prop -> Prop) (Sup.sup.{0} Prop (SemilatticeSup.toHasSup.{0} Prop (Lattice.toSemilatticeSup.{0} Prop (LinearOrder.toLattice.{0} Prop Prop.linearOrder)))) Or
but is expected to have type
  Eq.{1} (Prop -> Prop -> Prop) (fun (x._@.Mathlib.Order.PropInstances._hyg.236 : Prop) (x._@.Mathlib.Order.PropInstances._hyg.238 : Prop) => Sup.sup.{0} Prop (SemilatticeSup.toSup.{0} Prop (Lattice.toSemilatticeSup.{0} Prop (DistribLattice.toLattice.{0} Prop Prop.distribLattice))) x._@.Mathlib.Order.PropInstances._hyg.236 x._@.Mathlib.Order.PropInstances._hyg.238) (fun (x._@.Mathlib.Order.PropInstances._hyg.251 : Prop) (x._@.Mathlib.Order.PropInstances._hyg.253 : Prop) => Or x._@.Mathlib.Order.PropInstances._hyg.251 x._@.Mathlib.Order.PropInstances._hyg.253)
Case conversion may be inaccurate. Consider using '#align sup_Prop_eq sup_Prop_eqₓ'. -/
@[simp]
theorem sup_Prop_eq : (· ⊔ ·) = (· ∨ ·) :=
  rfl
#align sup_Prop_eq sup_Prop_eq

/- warning: inf_Prop_eq -> inf_Prop_eq is a dubious translation:
lean 3 declaration is
  Eq.{1} (Prop -> Prop -> Prop) (Inf.inf.{0} Prop (SemilatticeInf.toHasInf.{0} Prop (Lattice.toSemilatticeInf.{0} Prop (LinearOrder.toLattice.{0} Prop Prop.linearOrder)))) And
but is expected to have type
  Eq.{1} (Prop -> Prop -> Prop) (fun (x._@.Mathlib.Order.PropInstances._hyg.272 : Prop) (x._@.Mathlib.Order.PropInstances._hyg.274 : Prop) => Inf.inf.{0} Prop (Lattice.toInf.{0} Prop (DistribLattice.toLattice.{0} Prop Prop.distribLattice)) x._@.Mathlib.Order.PropInstances._hyg.272 x._@.Mathlib.Order.PropInstances._hyg.274) (fun (x._@.Mathlib.Order.PropInstances._hyg.287 : Prop) (x._@.Mathlib.Order.PropInstances._hyg.289 : Prop) => And x._@.Mathlib.Order.PropInstances._hyg.287 x._@.Mathlib.Order.PropInstances._hyg.289)
Case conversion may be inaccurate. Consider using '#align inf_Prop_eq inf_Prop_eqₓ'. -/
@[simp]
theorem inf_Prop_eq : (· ⊓ ·) = (· ∧ ·) :=
  rfl
#align inf_Prop_eq inf_Prop_eq

namespace Pi

variable {ι : Type _} {α' : ι → Type _} [∀ i, PartialOrder (α' i)]

/- warning: pi.disjoint_iff -> Pi.disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), OrderBot.{u2} (α' i) (Preorder.toHasLe.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (Disjoint.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.orderBot.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toHasLe.{u2} ((fun (i : ι) => (fun (i : ι) => (fun (i : ι) => α' i) i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), Disjoint.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
but is expected to have type
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), OrderBot.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (Disjoint.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.orderBot.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => α' i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), Disjoint.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align pi.disjoint_iff Pi.disjoint_iffₓ'. -/
theorem disjoint_iff [∀ i, OrderBot (α' i)] {f g : ∀ i, α' i} :
    Disjoint f g ↔ ∀ i, Disjoint (f i) (g i) :=
  by
  constructor
  · intro h i x hf hg
    classical
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
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), OrderTop.{u2} (α' i) (Preorder.toHasLe.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (Codisjoint.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.orderTop.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toHasLe.{u2} ((fun (i : ι) => (fun (i : ι) => (fun (i : ι) => α' i) i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), Codisjoint.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
but is expected to have type
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), OrderTop.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (Codisjoint.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.orderTop.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => α' i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), Codisjoint.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align pi.codisjoint_iff Pi.codisjoint_iffₓ'. -/
theorem codisjoint_iff [∀ i, OrderTop (α' i)] {f g : ∀ i, α' i} :
    Codisjoint f g ↔ ∀ i, Codisjoint (f i) (g i) :=
  @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _
#align pi.codisjoint_iff Pi.codisjoint_iff

/- warning: pi.is_compl_iff -> Pi.isCompl_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), BoundedOrder.{u2} (α' i) (Preorder.toHasLe.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (IsCompl.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.boundedOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toHasLe.{u2} ((fun (i : ι) => (fun (i : ι) => (fun (i : ι) => α' i) i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), IsCompl.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
but is expected to have type
  forall {ι : Type.{u1}} {α' : ι -> Type.{u2}} [_inst_1 : forall (i : ι), PartialOrder.{u2} (α' i)] [_inst_2 : forall (i : ι), BoundedOrder.{u2} (α' i) (Preorder.toLE.{u2} (α' i) (PartialOrder.toPreorder.{u2} (α' i) (_inst_1 i)))] {f : forall (i : ι), α' i} {g : forall (i : ι), α' i}, Iff (IsCompl.{max u1 u2} (forall (i : ι), α' i) (Pi.partialOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => _inst_1 i)) (Pi.boundedOrder.{u1, u2} ι (fun (i : ι) => α' i) (fun (i : ι) => Preorder.toLE.{u2} ((fun (i : ι) => (fun (i : ι) => α' i) i) i) ((fun (i : ι) => PartialOrder.toPreorder.{u2} ((fun (i : ι) => α' i) i) ((fun (i : ι) => _inst_1 i) i)) i)) (fun (i : ι) => _inst_2 i)) f g) (forall (i : ι), IsCompl.{u2} (α' i) (_inst_1 i) (_inst_2 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align pi.is_compl_iff Pi.isCompl_iffₓ'. -/
theorem isCompl_iff [∀ i, BoundedOrder (α' i)] {f g : ∀ i, α' i} :
    IsCompl f g ↔ ∀ i, IsCompl (f i) (g i) := by
  simp_rw [isCompl_iff, disjoint_iff, codisjoint_iff, forall_and]
#align pi.is_compl_iff Pi.isCompl_iff

end Pi

#print Prop.disjoint_iff /-
@[simp]
theorem Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q) :=
  disjoint_iff_inf_le
#align Prop.disjoint_iff Prop.disjoint_iff
-/

#print Prop.codisjoint_iff /-
@[simp]
theorem Prop.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q :=
  codisjoint_iff_le_sup.trans <| forall_const _
#align Prop.codisjoint_iff Prop.codisjoint_iff
-/

#print Prop.isCompl_iff /-
@[simp]
theorem Prop.isCompl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q) :=
  by
  rw [isCompl_iff, Prop.disjoint_iff, Prop.codisjoint_iff, not_iff]
  classical tauto
#align Prop.is_compl_iff Prop.isCompl_iff
-/

