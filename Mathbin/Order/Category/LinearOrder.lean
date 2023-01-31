/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.category.LinearOrder
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.Lattice

/-!
# Category of linear orders

This defines `LinearOrder`, the category of linear orders with monotone maps.
-/


open CategoryTheory

universe u

/-- The category of linear orders. -/
def LinearOrderCat :=
  Bundled LinearOrder
#align LinearOrder LinearOrderCat

namespace LinearOrderCat

instance : BundledHom.ParentProjection @LinearOrder.toPartialOrder :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for LinearOrderCat

instance : CoeSort LinearOrderCat (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `LinearOrder` from the underlying type and typeclass. -/
def of (α : Type _) [LinearOrder α] : LinearOrderCat :=
  Bundled.of α
#align LinearOrder.of LinearOrderCat.of

@[simp]
theorem coe_of (α : Type _) [LinearOrder α] : ↥(of α) = α :=
  rfl
#align LinearOrder.coe_of LinearOrderCat.coe_of

instance : Inhabited LinearOrderCat :=
  ⟨of PUnit⟩

instance (α : LinearOrderCat) : LinearOrder α :=
  α.str

instance hasForgetToLattice : HasForget₂ LinearOrderCat LatticeCat
    where forget₂ :=
    { obj := fun X => LatticeCat.of X
      map := fun X Y f => (OrderHomClass.toLatticeHom X Y f : LatticeHom X Y) }
#align LinearOrder.has_forget_to_Lattice LinearOrderCat.hasForgetToLattice

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : LinearOrderCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply x
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply x
#align LinearOrder.iso.mk LinearOrderCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : LinearOrderCat ⥤ LinearOrderCat
    where
  obj X := of Xᵒᵈ
  map X Y := OrderHom.dual
#align LinearOrder.dual LinearOrderCat.dual

/-- The equivalence between `LinearOrder` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : LinearOrderCat ≌ LinearOrderCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align LinearOrder.dual_equiv LinearOrderCat.dualEquiv

end LinearOrderCat

theorem linearOrderCat_dual_comp_forget_to_latticeCat :
    LinearOrderCat.dual ⋙ forget₂ LinearOrderCat LatticeCat =
      forget₂ LinearOrderCat LatticeCat ⋙ LatticeCat.dual :=
  rfl
#align LinearOrder_dual_comp_forget_to_Lattice linearOrderCat_dual_comp_forget_to_latticeCat

