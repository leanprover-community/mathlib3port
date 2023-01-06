/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BoundedLattice
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.BoundedOrderCat
import Mathbin.Order.Category.LatticeCat
import Mathbin.Order.Category.SemilatticeCat

/-!
# The category of bounded lattices

This file defines `BoundedLattice`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BoundedLatticeCat where
  toLattice : LatticeCat
  [isBoundedOrder : BoundedOrder to_Lattice]
#align BoundedLattice BoundedLatticeCat

namespace BoundedLatticeCat

instance : CoeSort BoundedLatticeCat (Type _) :=
  ⟨fun X => X.toLattice⟩

instance (X : BoundedLatticeCat) : Lattice X :=
  X.toLattice.str

attribute [instance] BoundedLatticeCat.isBoundedOrder

/-- Construct a bundled `BoundedLattice` from `lattice` + `bounded_order`. -/
def of (α : Type _) [Lattice α] [BoundedOrder α] : BoundedLatticeCat :=
  ⟨⟨α⟩⟩
#align BoundedLattice.of BoundedLatticeCat.of

@[simp]
theorem coe_of (α : Type _) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BoundedLattice.coe_of BoundedLatticeCat.coe_of

instance : Inhabited BoundedLatticeCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} BoundedLatticeCat
    where
  Hom X Y := BoundedLatticeHom X Y
  id X := BoundedLatticeHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := BoundedLatticeHom.comp_id
  comp_id' X Y := BoundedLatticeHom.id_comp
  assoc' W X Y Z _ _ _ := BoundedLatticeHom.comp_assoc _ _ _

instance : ConcreteCategory BoundedLatticeCat
    where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y => by convert FunLike.coe_injective⟩

instance hasForgetToBoundedOrder : HasForget₂ BoundedLatticeCat BoundedOrderCat
    where forget₂ :=
    { obj := fun X => BoundedOrderCat.of X
      map := fun X Y => BoundedLatticeHom.toBoundedOrderHom }
#align BoundedLattice.has_forget_to_BoundedOrder BoundedLatticeCat.hasForgetToBoundedOrder

instance hasForgetToLattice : HasForget₂ BoundedLatticeCat LatticeCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BoundedLattice.has_forget_to_Lattice BoundedLatticeCat.hasForgetToLattice

instance hasForgetToSemilatticeSup : HasForget₂ BoundedLatticeCat SemilatticeSupCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toSupBotHom }
#align BoundedLattice.has_forget_to_SemilatticeSup BoundedLatticeCat.hasForgetToSemilatticeSup

instance hasForgetToSemilatticeInf : HasForget₂ BoundedLatticeCat SemilatticeInfCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toInfTopHom }
#align BoundedLattice.has_forget_to_SemilatticeInf BoundedLatticeCat.hasForgetToSemilatticeInf

@[simp]
theorem coe_forget_to_BoundedOrder (X : BoundedLatticeCat) :
    ↥((forget₂ BoundedLatticeCat BoundedOrderCat).obj X) = ↥X :=
  rfl
#align BoundedLattice.coe_forget_to_BoundedOrder BoundedLatticeCat.coe_forget_to_BoundedOrder

@[simp]
theorem coe_forget_to_Lattice (X : BoundedLatticeCat) :
    ↥((forget₂ BoundedLatticeCat LatticeCat).obj X) = ↥X :=
  rfl
#align BoundedLattice.coe_forget_to_Lattice BoundedLatticeCat.coe_forget_to_Lattice

@[simp]
theorem coe_forget_to_SemilatticeSup (X : BoundedLatticeCat) :
    ↥((forget₂ BoundedLatticeCat SemilatticeSupCat).obj X) = ↥X :=
  rfl
#align BoundedLattice.coe_forget_to_SemilatticeSup BoundedLatticeCat.coe_forget_to_SemilatticeSup

@[simp]
theorem coe_forget_to_SemilatticeInf (X : BoundedLatticeCat) :
    ↥((forget₂ BoundedLatticeCat SemilatticeInfCat).obj X) = ↥X :=
  rfl
#align BoundedLattice.coe_forget_to_SemilatticeInf BoundedLatticeCat.coe_forget_to_SemilatticeInf

theorem forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
    forget₂ BoundedLatticeCat LatticeCat ⋙ forget₂ LatticeCat PartialOrderCat =
      forget₂ BoundedLatticeCat BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderCat :=
  rfl
#align
  BoundedLattice.forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder BoundedLatticeCat.forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder

theorem forget_SemilatticeSup_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
    forget₂ BoundedLatticeCat SemilatticeSupCat ⋙ forget₂ SemilatticeSupCat PartialOrderCat =
      forget₂ BoundedLatticeCat BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderCat :=
  rfl
#align
  BoundedLattice.forget_SemilatticeSup_PartialOrder_eq_forget_BoundedOrder_PartialOrder BoundedLatticeCat.forget_SemilatticeSup_PartialOrder_eq_forget_BoundedOrder_PartialOrder

theorem forget_SemilatticeInf_PartialOrder_eq_forget_BoundedOrder_PartialOrder :
    forget₂ BoundedLatticeCat SemilatticeInfCat ⋙ forget₂ SemilatticeInfCat PartialOrderCat =
      forget₂ BoundedLatticeCat BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderCat :=
  rfl
#align
  BoundedLattice.forget_SemilatticeInf_PartialOrder_eq_forget_BoundedOrder_PartialOrder BoundedLatticeCat.forget_SemilatticeInf_PartialOrder_eq_forget_BoundedOrder_PartialOrder

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BoundedLatticeCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align BoundedLattice.iso.mk BoundedLatticeCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoundedLatticeCat ⥤ BoundedLatticeCat
    where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BoundedLattice.dual BoundedLatticeCat.dual

/-- The equivalence between `BoundedLattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoundedLatticeCat ≌ BoundedLatticeCat :=
  Equivalence.mk dual dual
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    ((NatIso.ofComponents fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BoundedLattice.dual_equiv BoundedLatticeCat.dualEquiv

end BoundedLatticeCat

theorem BoundedLattice_dual_comp_forget_to_BoundedOrder :
    BoundedLatticeCat.dual ⋙ forget₂ BoundedLatticeCat BoundedOrderCat =
      forget₂ BoundedLatticeCat BoundedOrderCat ⋙ BoundedOrderCat.dual :=
  rfl
#align
  BoundedLattice_dual_comp_forget_to_BoundedOrder BoundedLattice_dual_comp_forget_to_BoundedOrder

theorem BoundedLattice_dual_comp_forget_to_Lattice :
    BoundedLatticeCat.dual ⋙ forget₂ BoundedLatticeCat LatticeCat =
      forget₂ BoundedLatticeCat LatticeCat ⋙ LatticeCat.dual :=
  rfl
#align BoundedLattice_dual_comp_forget_to_Lattice BoundedLattice_dual_comp_forget_to_Lattice

theorem BoundedLattice_dual_comp_forget_to_SemilatticeSup :
    BoundedLatticeCat.dual ⋙ forget₂ BoundedLatticeCat SemilatticeSupCat =
      forget₂ BoundedLatticeCat SemilatticeInfCat ⋙ SemilatticeInfCat.dual :=
  rfl
#align
  BoundedLattice_dual_comp_forget_to_SemilatticeSup BoundedLattice_dual_comp_forget_to_SemilatticeSup

theorem BoundedLattice_dual_comp_forget_to_SemilatticeInf :
    BoundedLatticeCat.dual ⋙ forget₂ BoundedLatticeCat SemilatticeInfCat =
      forget₂ BoundedLatticeCat SemilatticeSupCat ⋙ SemilatticeSupCat.dual :=
  rfl
#align
  BoundedLattice_dual_comp_forget_to_SemilatticeInf BoundedLattice_dual_comp_forget_to_SemilatticeInf

