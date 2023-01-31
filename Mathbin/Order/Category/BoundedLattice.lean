/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BoundedLattice
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.BoundedOrder
import Mathbin.Order.Category.Lattice
import Mathbin.Order.Category.Semilattice

/-!
# The category of bounded lattices

This file defines `BoundedLattice`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BoundedLattice where
  toLattice : LatticeCat
  [isBoundedOrder : BoundedOrder to_Lattice]
#align BoundedLattice BoundedLattice

namespace BoundedLattice

instance : CoeSort BoundedLattice (Type _) :=
  ⟨fun X => X.toLattice⟩

instance (X : BoundedLattice) : Lattice X :=
  X.toLattice.str

attribute [instance] BoundedLattice.isBoundedOrder

/-- Construct a bundled `BoundedLattice` from `lattice` + `bounded_order`. -/
def of (α : Type _) [Lattice α] [BoundedOrder α] : BoundedLattice :=
  ⟨⟨α⟩⟩
#align BoundedLattice.of BoundedLattice.of

@[simp]
theorem coe_of (α : Type _) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BoundedLattice.coe_of BoundedLattice.coe_of

instance : Inhabited BoundedLattice :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} BoundedLattice
    where
  Hom X Y := BoundedLatticeHom X Y
  id X := BoundedLatticeHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := BoundedLatticeHom.comp_id
  comp_id' X Y := BoundedLatticeHom.id_comp
  assoc' W X Y Z _ _ _ := BoundedLatticeHom.comp_assoc _ _ _

instance : ConcreteCategory BoundedLattice
    where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y => by convert FunLike.coe_injective⟩

instance hasForgetToBoundedOrder : HasForget₂ BoundedLattice BoundedOrderCat
    where forget₂ :=
    { obj := fun X => BoundedOrderCat.of X
      map := fun X Y => BoundedLatticeHom.toBoundedOrderHom }
#align BoundedLattice.has_forget_to_BoundedOrder BoundedLattice.hasForgetToBoundedOrder

instance hasForgetToLattice : HasForget₂ BoundedLattice LatticeCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BoundedLattice.has_forget_to_Lattice BoundedLattice.hasForgetToLattice

instance hasForgetToSemilatticeSup : HasForget₂ BoundedLattice SemilatticeSupCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toSupBotHom }
#align BoundedLattice.has_forget_to_SemilatticeSup BoundedLattice.hasForgetToSemilatticeSup

instance hasForgetToSemilatticeInf : HasForget₂ BoundedLattice SemilatticeInfCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toInfTopHom }
#align BoundedLattice.has_forget_to_SemilatticeInf BoundedLattice.hasForgetToSemilatticeInf

@[simp]
theorem coe_forget_to_boundedOrderCat (X : BoundedLattice) :
    ↥((forget₂ BoundedLattice BoundedOrderCat).obj X) = ↥X :=
  rfl
#align BoundedLattice.coe_forget_to_BoundedOrder BoundedLattice.coe_forget_to_boundedOrderCat

@[simp]
theorem coe_forget_to_latticeCat (X : BoundedLattice) :
    ↥((forget₂ BoundedLattice LatticeCat).obj X) = ↥X :=
  rfl
#align BoundedLattice.coe_forget_to_Lattice BoundedLattice.coe_forget_to_latticeCat

@[simp]
theorem coe_forget_to_semilatticeSupCat (X : BoundedLattice) :
    ↥((forget₂ BoundedLattice SemilatticeSupCat).obj X) = ↥X :=
  rfl
#align BoundedLattice.coe_forget_to_SemilatticeSup BoundedLattice.coe_forget_to_semilatticeSupCat

@[simp]
theorem coe_forget_to_semilatticeInfCat (X : BoundedLattice) :
    ↥((forget₂ BoundedLattice SemilatticeInfCat).obj X) = ↥X :=
  rfl
#align BoundedLattice.coe_forget_to_SemilatticeInf BoundedLattice.coe_forget_to_semilatticeInfCat

theorem forget_latticeCat_partialOrderCat_eq_forget_boundedOrderCat_partialOrderCat :
    forget₂ BoundedLattice LatticeCat ⋙ forget₂ LatticeCat PartialOrderCat =
      forget₂ BoundedLattice BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderCat :=
  rfl
#align BoundedLattice.forget_Lattice_PartialOrder_eq_forget_BoundedOrder_PartialOrder BoundedLattice.forget_latticeCat_partialOrderCat_eq_forget_boundedOrderCat_partialOrderCat

theorem forget_semilatticeSupCat_partialOrderCat_eq_forget_boundedOrderCat_partialOrderCat :
    forget₂ BoundedLattice SemilatticeSupCat ⋙ forget₂ SemilatticeSupCat PartialOrderCat =
      forget₂ BoundedLattice BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderCat :=
  rfl
#align BoundedLattice.forget_SemilatticeSup_PartialOrder_eq_forget_BoundedOrder_PartialOrder BoundedLattice.forget_semilatticeSupCat_partialOrderCat_eq_forget_boundedOrderCat_partialOrderCat

theorem forget_semilatticeInfCat_partialOrderCat_eq_forget_boundedOrderCat_partialOrderCat :
    forget₂ BoundedLattice SemilatticeInfCat ⋙ forget₂ SemilatticeInfCat PartialOrderCat =
      forget₂ BoundedLattice BoundedOrderCat ⋙ forget₂ BoundedOrderCat PartialOrderCat :=
  rfl
#align BoundedLattice.forget_SemilatticeInf_PartialOrder_eq_forget_BoundedOrder_PartialOrder BoundedLattice.forget_semilatticeInfCat_partialOrderCat_eq_forget_boundedOrderCat_partialOrderCat

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BoundedLattice.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align BoundedLattice.iso.mk BoundedLattice.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : BoundedLattice ⥤ BoundedLattice
    where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BoundedLattice.dual BoundedLattice.dual

/-- The equivalence between `BoundedLattice` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BoundedLattice ≌ BoundedLattice :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BoundedLattice.dual_equiv BoundedLattice.dualEquiv

end BoundedLattice

theorem boundedLattice_dual_comp_forget_to_boundedOrderCat :
    BoundedLattice.dual ⋙ forget₂ BoundedLattice BoundedOrderCat =
      forget₂ BoundedLattice BoundedOrderCat ⋙ BoundedOrderCat.dual :=
  rfl
#align BoundedLattice_dual_comp_forget_to_BoundedOrder boundedLattice_dual_comp_forget_to_boundedOrderCat

theorem boundedLattice_dual_comp_forget_to_latticeCat :
    BoundedLattice.dual ⋙ forget₂ BoundedLattice LatticeCat =
      forget₂ BoundedLattice LatticeCat ⋙ LatticeCat.dual :=
  rfl
#align BoundedLattice_dual_comp_forget_to_Lattice boundedLattice_dual_comp_forget_to_latticeCat

theorem boundedLattice_dual_comp_forget_to_semilatticeSupCat :
    BoundedLattice.dual ⋙ forget₂ BoundedLattice SemilatticeSupCat =
      forget₂ BoundedLattice SemilatticeInfCat ⋙ SemilatticeInfCat.dual :=
  rfl
#align BoundedLattice_dual_comp_forget_to_SemilatticeSup boundedLattice_dual_comp_forget_to_semilatticeSupCat

theorem boundedLattice_dual_comp_forget_to_semilatticeInfCat :
    BoundedLattice.dual ⋙ forget₂ BoundedLattice SemilatticeInfCat =
      forget₂ BoundedLattice SemilatticeSupCat ⋙ SemilatticeSupCat.dual :=
  rfl
#align BoundedLattice_dual_comp_forget_to_SemilatticeInf boundedLattice_dual_comp_forget_to_semilatticeInfCat

