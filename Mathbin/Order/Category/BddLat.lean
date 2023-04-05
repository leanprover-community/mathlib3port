/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.BddLat
! leanprover-community/mathlib commit e8ac6315bcfcbaf2d19a046719c3b553206dac75
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.BddOrd
import Mathbin.Order.Category.Lat
import Mathbin.Order.Category.Semilat

/-!
# The category of bounded lattices

This file defines `BddLat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BddLat where
  toLat : LatCat
  [isBoundedOrder : BoundedOrder to_Lat]
#align BddLat BddLat

namespace BddLat

instance : CoeSort BddLat (Type _) :=
  ⟨fun X => X.toLat⟩

instance (X : BddLat) : Lattice X :=
  X.toLat.str

attribute [instance] BddLat.isBoundedOrder

/-- Construct a bundled `BddLat` from `lattice` + `bounded_order`. -/
def of (α : Type _) [Lattice α] [BoundedOrder α] : BddLat :=
  ⟨⟨α⟩⟩
#align BddLat.of BddLat.of

@[simp]
theorem coe_of (α : Type _) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddLat.coe_of BddLat.coe_of

instance : Inhabited BddLat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} BddLat
    where
  Hom X Y := BoundedLatticeHom X Y
  id X := BoundedLatticeHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := BoundedLatticeHom.comp_id
  comp_id' X Y := BoundedLatticeHom.id_comp
  assoc' W X Y Z _ _ _ := BoundedLatticeHom.comp_assoc _ _ _

instance : ConcreteCategory BddLat
    where
  forget := ⟨coeSort, fun X Y => coeFn, fun X => rfl, fun X Y Z f g => rfl⟩
  forget_faithful := ⟨fun X Y => by convert FunLike.coe_injective⟩

instance hasForgetToBddOrd : HasForget₂ BddLat BddOrd
    where forget₂ :=
    { obj := fun X => BddOrd.of X
      map := fun X Y => BoundedLatticeHom.toBoundedOrderHom }
#align BddLat.has_forget_to_BddOrd BddLat.hasForgetToBddOrd

instance hasForgetToLat : HasForget₂ BddLat LatCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BddLat.has_forget_to_Lat BddLat.hasForgetToLat

instance hasForgetToSemilatSup : HasForget₂ BddLat SemilatSup
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toSupBotHom }
#align BddLat.has_forget_to_SemilatSup BddLat.hasForgetToSemilatSup

instance hasForgetToSemilatInf : HasForget₂ BddLat SemilatInf
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toInfTopHom }
#align BddLat.has_forget_to_SemilatInf BddLat.hasForgetToSemilatInf

@[simp]
theorem coe_forget_to_bddOrd (X : BddLat) : ↥((forget₂ BddLat BddOrd).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_BddOrd BddLat.coe_forget_to_bddOrd

@[simp]
theorem coe_forget_to_latCat (X : BddLat) : ↥((forget₂ BddLat LatCat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_Lat BddLat.coe_forget_to_latCat

@[simp]
theorem coe_forget_to_semilatSup (X : BddLat) : ↥((forget₂ BddLat SemilatSup).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_SemilatSup BddLat.coe_forget_to_semilatSup

@[simp]
theorem coe_forget_to_semilatInf (X : BddLat) : ↥((forget₂ BddLat SemilatInf).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_SemilatInf BddLat.coe_forget_to_semilatInf

theorem forget_latCat_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLat LatCat ⋙ forget₂ LatCat PartOrdCat =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrdCat :=
  rfl
#align BddLat.forget_Lat_PartOrd_eq_forget_BddOrd_PartOrd BddLat.forget_latCat_partOrdCat_eq_forget_bddOrd_partOrdCat

theorem forget_semilatSup_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLat SemilatSup ⋙ forget₂ SemilatSup PartOrdCat =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrdCat :=
  rfl
#align BddLat.forget_SemilatSup_PartOrd_eq_forget_BddOrd_PartOrd BddLat.forget_semilatSup_partOrdCat_eq_forget_bddOrd_partOrdCat

theorem forget_semilatInf_partOrdCat_eq_forget_bddOrd_partOrdCat :
    forget₂ BddLat SemilatInf ⋙ forget₂ SemilatInf PartOrdCat =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrdCat :=
  rfl
#align BddLat.forget_SemilatInf_PartOrd_eq_forget_BddOrd_PartOrd BddLat.forget_semilatInf_partOrdCat_eq_forget_bddOrd_partOrdCat

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddLat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align BddLat.iso.mk BddLat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : BddLat ⥤ BddLat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BddLat.dual BddLat.dual

/-- The equivalence between `BddLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddLat ≌ BddLat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddLat.dual_equiv BddLat.dualEquiv

end BddLat

theorem bddLat_dual_comp_forget_to_bddOrd :
    BddLat.dual ⋙ forget₂ BddLat BddOrd = forget₂ BddLat BddOrd ⋙ BddOrd.dual :=
  rfl
#align BddLat_dual_comp_forget_to_BddOrd bddLat_dual_comp_forget_to_bddOrd

theorem bddLat_dual_comp_forget_to_latCat :
    BddLat.dual ⋙ forget₂ BddLat LatCat = forget₂ BddLat LatCat ⋙ LatCat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_Lat bddLat_dual_comp_forget_to_latCat

theorem bddLat_dual_comp_forget_to_semilatSup :
    BddLat.dual ⋙ forget₂ BddLat SemilatSup = forget₂ BddLat SemilatInf ⋙ SemilatInf.dual :=
  rfl
#align BddLat_dual_comp_forget_to_SemilatSup bddLat_dual_comp_forget_to_semilatSup

theorem bddLat_dual_comp_forget_to_semilatInf :
    BddLat.dual ⋙ forget₂ BddLat SemilatInf = forget₂ BddLat SemilatSup ⋙ SemilatSup.dual :=
  rfl
#align BddLat_dual_comp_forget_to_SemilatInf bddLat_dual_comp_forget_to_semilatInf

