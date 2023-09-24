/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import CategoryTheory.Adjunction.Opposites
import Order.Category.BddOrd
import Order.Category.Lat
import Order.Category.Semilat

#align_import order.category.BddLat from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

/-!
# The category of bounded lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `BddLat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/


universe u

open CategoryTheory

#print BddLat /-
/-- The category of bounded lattices with bounded lattice morphisms. -/
structure BddLat where
  toLat : Lat
  [isBoundedOrder : BoundedOrder to_Lat]
#align BddLat BddLat
-/

namespace BddLat

instance : CoeSort BddLat (Type _) :=
  ⟨fun X => X.toLat⟩

instance (X : BddLat) : Lattice X :=
  X.toLat.str

attribute [instance] BddLat.isBoundedOrder

#print BddLat.of /-
/-- Construct a bundled `BddLat` from `lattice` + `bounded_order`. -/
def of (α : Type _) [Lattice α] [BoundedOrder α] : BddLat :=
  ⟨⟨α⟩⟩
#align BddLat.of BddLat.of
-/

#print BddLat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl
#align BddLat.coe_of BddLat.coe_of
-/

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

#print BddLat.hasForgetToBddOrd /-
instance hasForgetToBddOrd : HasForget₂ BddLat BddOrd
    where forget₂ :=
    { obj := fun X => BddOrd.of X
      map := fun X Y => BoundedLatticeHom.toBoundedOrderHom }
#align BddLat.has_forget_to_BddOrd BddLat.hasForgetToBddOrd
-/

#print BddLat.hasForgetToLat /-
instance hasForgetToLat : HasForget₂ BddLat Lat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toLatticeHom }
#align BddLat.has_forget_to_Lat BddLat.hasForgetToLat
-/

#print BddLat.hasForgetToSemilatSup /-
instance hasForgetToSemilatSup : HasForget₂ BddLat SemilatSupCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toSupBotHom }
#align BddLat.has_forget_to_SemilatSup BddLat.hasForgetToSemilatSup
-/

#print BddLat.hasForgetToSemilatInf /-
instance hasForgetToSemilatInf : HasForget₂ BddLat SemilatInfCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y => BoundedLatticeHom.toInfTopHom }
#align BddLat.has_forget_to_SemilatInf BddLat.hasForgetToSemilatInf
-/

#print BddLat.coe_forget_to_bddOrd /-
@[simp]
theorem coe_forget_to_bddOrd (X : BddLat) : ↥((forget₂ BddLat BddOrd).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_BddOrd BddLat.coe_forget_to_bddOrd
-/

#print BddLat.coe_forget_to_lat /-
@[simp]
theorem coe_forget_to_lat (X : BddLat) : ↥((forget₂ BddLat Lat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_Lat BddLat.coe_forget_to_lat
-/

#print BddLat.coe_forget_to_semilatSup /-
@[simp]
theorem coe_forget_to_semilatSup (X : BddLat) : ↥((forget₂ BddLat SemilatSupCat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_SemilatSup BddLat.coe_forget_to_semilatSup
-/

#print BddLat.coe_forget_to_semilatInf /-
@[simp]
theorem coe_forget_to_semilatInf (X : BddLat) : ↥((forget₂ BddLat SemilatInfCat).obj X) = ↥X :=
  rfl
#align BddLat.coe_forget_to_SemilatInf BddLat.coe_forget_to_semilatInf
-/

#print BddLat.forget_lat_partOrd_eq_forget_bddOrd_partOrd /-
theorem forget_lat_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat Lat ⋙ forget₂ Lat PartOrd = forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl
#align BddLat.forget_Lat_PartOrd_eq_forget_BddOrd_PartOrd BddLat.forget_lat_partOrd_eq_forget_bddOrd_partOrd
-/

#print BddLat.forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd /-
theorem forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat SemilatSupCat ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl
#align BddLat.forget_SemilatSup_PartOrd_eq_forget_BddOrd_PartOrd BddLat.forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd
-/

#print BddLat.forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd /-
theorem forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat SemilatInfCat ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl
#align BddLat.forget_SemilatInf_PartOrd_eq_forget_BddOrd_PartOrd BddLat.forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd
-/

#print BddLat.Iso.mk /-
/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
def Iso.mk {α β : BddLat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align BddLat.iso.mk BddLat.Iso.mk
-/

#print BddLat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : BddLat ⥤ BddLat where
  obj X := of Xᵒᵈ
  map X Y := BoundedLatticeHom.dual
#align BddLat.dual BddLat.dual
-/

#print BddLat.dualEquiv /-
/-- The equivalence between `BddLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : BddLat ≌ BddLat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align BddLat.dual_equiv BddLat.dualEquiv
-/

end BddLat

#print bddLat_dual_comp_forget_to_bddOrd /-
theorem bddLat_dual_comp_forget_to_bddOrd :
    BddLat.dual ⋙ forget₂ BddLat BddOrd = forget₂ BddLat BddOrd ⋙ BddOrd.dual :=
  rfl
#align BddLat_dual_comp_forget_to_BddOrd bddLat_dual_comp_forget_to_bddOrd
-/

#print bddLat_dual_comp_forget_to_lat /-
theorem bddLat_dual_comp_forget_to_lat :
    BddLat.dual ⋙ forget₂ BddLat Lat = forget₂ BddLat Lat ⋙ Lat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_Lat bddLat_dual_comp_forget_to_lat
-/

#print bddLat_dual_comp_forget_to_semilatSupCat /-
theorem bddLat_dual_comp_forget_to_semilatSupCat :
    BddLat.dual ⋙ forget₂ BddLat SemilatSupCat =
      forget₂ BddLat SemilatInfCat ⋙ SemilatInfCat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_SemilatSup bddLat_dual_comp_forget_to_semilatSupCat
-/

#print bddLat_dual_comp_forget_to_semilatInfCat /-
theorem bddLat_dual_comp_forget_to_semilatInfCat :
    BddLat.dual ⋙ forget₂ BddLat SemilatInfCat =
      forget₂ BddLat SemilatSupCat ⋙ SemilatSupCat.dual :=
  rfl
#align BddLat_dual_comp_forget_to_SemilatInf bddLat_dual_comp_forget_to_semilatInfCat
-/

#print latToBddLat /-
/-- The functor that adds a bottom and a top element to a lattice. This is the free functor. -/
def latToBddLat : Lat.{u} ⥤ BddLat
    where
  obj X := BddLat.of <| WithTop <| WithBot X
  map X Y := LatticeHom.withTopWithBot
  map_id' X := LatticeHom.withTopWithBot_id
  map_comp' X Y Z _ _ := LatticeHom.withTopWithBot_comp _ _
#align Lat_to_BddLat latToBddLat
-/

#print latToBddLatForgetAdjunction /-
/-- `Lat_to_BddLat` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lat` to `BddLat`. -/
def latToBddLatForgetAdjunction : latToBddLat.{u} ⊣ forget₂ BddLat Lat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { toFun := f ∘ some ∘ some
              map_sup' := fun a b => (congr_arg f <| by rfl).trans (f.map_sup' _ _)
              map_inf' := fun a b => (congr_arg f <| by rfl).trans (f.map_inf' _ _) }
          invFun := LatticeHom.withTopWithBot'
          left_inv := fun f =>
            BoundedLatticeHom.ext fun a =>
              match a with
              | none => f.map_top'.symm
              | some none => f.map_bot'.symm
              | some (some a) => rfl
          right_inv := fun f => LatticeHom.ext fun a => rfl }
      homEquiv_naturality_left_symm := fun X Y Z f g =>
        BoundedLatticeHom.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some a) => rfl
      homEquiv_naturality_right := fun X Y Z f g => LatticeHom.ext fun a => rfl }
#align Lat_to_BddLat_forget_adjunction latToBddLatForgetAdjunction
-/

#print latToBddLatCompDualIsoDualCompLatToBddLat /-
/-- `Lat_to_BddLat` and `order_dual` commute. -/
@[simps]
def latToBddLatCompDualIsoDualCompLatToBddLat :
    latToBddLat.{u} ⋙ BddLat.dual ≅ Lat.dual ⋙ latToBddLat :=
  Adjunction.leftAdjointUniq (latToBddLatForgetAdjunction.comp BddLat.dualEquiv.toAdjunction)
    (Lat.dualEquiv.toAdjunction.comp latToBddLatForgetAdjunction)
#align Lat_to_BddLat_comp_dual_iso_dual_comp_Lat_to_BddLat latToBddLatCompDualIsoDualCompLatToBddLat
-/

