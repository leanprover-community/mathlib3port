/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.Semilattice
! leanprover-community/mathlib commit 9830a300340708eaa85d477c3fb96dd25f9468a5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.PartialOrderCat
import Mathbin.Order.Hom.Lattice

/-!
# The categories of semilattices

This defines `SemilatticeSup` and `SemilatticeInf`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/


universe u

open CategoryTheory

/-- The category of sup-semilattices with a bottom element. -/
structure SemilatticeSupCat : Type (u + 1) where
  x : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot X]
#align SemilatticeSup SemilatticeSupCat

/-- The category of inf-semilattices with a top element. -/
structure SemilatticeInfCat : Type (u + 1) where
  x : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop X]
#align SemilatticeInf SemilatticeInfCat

attribute [protected] SemilatticeSupCat.X SemilatticeInfCat.X

namespace SemilatticeSupCat

instance : CoeSort SemilatticeSupCat (Type _) :=
  ⟨SemilatticeSupCat.X⟩

attribute [instance] is_semilattice_sup is_order_bot

/-- Construct a bundled `SemilatticeSup` from a `semilattice_sup`. -/
def of (α : Type _) [SemilatticeSup α] [OrderBot α] : SemilatticeSupCat :=
  ⟨α⟩
#align SemilatticeSup.of SemilatticeSupCat.of

@[simp]
theorem coe_of (α : Type _) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl
#align SemilatticeSup.coe_of SemilatticeSupCat.coe_of

instance : Inhabited SemilatticeSupCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatticeSupCat
    where
  Hom X Y := SupBotHom X Y
  id X := SupBotHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := SupBotHom.comp_id
  comp_id' X Y := SupBotHom.id_comp
  assoc' W X Y Z _ _ _ := SupBotHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatticeSupCat
    where
  forget :=
    { obj := SemilatticeSupCat.X
      map := fun X Y => coeFn }
  forget_faithful := ⟨fun X Y => FunLike.coe_injective⟩

instance hasForgetToPartialOrder : HasForget₂ SemilatticeSupCat PartialOrderCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
#align SemilatticeSup.has_forget_to_PartialOrder SemilatticeSupCat.hasForgetToPartialOrder

@[simp]
theorem coe_forget_to_PartialOrder (X : SemilatticeSupCat) :
    ↥((forget₂ SemilatticeSupCat PartialOrderCat).obj X) = ↥X :=
  rfl
#align SemilatticeSup.coe_forget_to_PartialOrder SemilatticeSupCat.coe_forget_to_PartialOrder

end SemilatticeSupCat

namespace SemilatticeInfCat

instance : CoeSort SemilatticeInfCat (Type _) :=
  ⟨SemilatticeInfCat.X⟩

attribute [instance] is_semilattice_inf is_order_top

/-- Construct a bundled `SemilatticeInf` from a `semilattice_inf`. -/
def of (α : Type _) [SemilatticeInf α] [OrderTop α] : SemilatticeInfCat :=
  ⟨α⟩
#align SemilatticeInf.of SemilatticeInfCat.of

@[simp]
theorem coe_of (α : Type _) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl
#align SemilatticeInf.coe_of SemilatticeInfCat.coe_of

instance : Inhabited SemilatticeInfCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatticeInfCat
    where
  Hom X Y := InfTopHom X Y
  id X := InfTopHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := InfTopHom.comp_id
  comp_id' X Y := InfTopHom.id_comp
  assoc' W X Y Z _ _ _ := InfTopHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatticeInfCat
    where
  forget :=
    { obj := SemilatticeInfCat.X
      map := fun X Y => coeFn }
  forget_faithful := ⟨fun X Y => FunLike.coe_injective⟩

instance hasForgetToPartialOrder : HasForget₂ SemilatticeInfCat PartialOrderCat
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
#align SemilatticeInf.has_forget_to_PartialOrder SemilatticeInfCat.hasForgetToPartialOrder

@[simp]
theorem coe_forget_to_PartialOrder (X : SemilatticeInfCat) :
    ↥((forget₂ SemilatticeInfCat PartialOrderCat).obj X) = ↥X :=
  rfl
#align SemilatticeInf.coe_forget_to_PartialOrder SemilatticeInfCat.coe_forget_to_PartialOrder

end SemilatticeInfCat

/-! ### Order dual -/


namespace SemilatticeSupCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatticeSupCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align SemilatticeSup.iso.mk SemilatticeSupCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : SemilatticeSupCat ⥤ SemilatticeInfCat
    where
  obj X := SemilatticeInfCat.of Xᵒᵈ
  map X Y := SupBotHom.dual
#align SemilatticeSup.dual SemilatticeSupCat.dual

end SemilatticeSupCat

namespace SemilatticeInfCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatticeInfCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id' := by
    ext
    exact e.apply_symm_apply _
#align SemilatticeInf.iso.mk SemilatticeInfCat.Iso.mk

/-- `order_dual` as a functor. -/
@[simps]
def dual : SemilatticeInfCat ⥤ SemilatticeSupCat
    where
  obj X := SemilatticeSupCat.of Xᵒᵈ
  map X Y := InfTopHom.dual
#align SemilatticeInf.dual SemilatticeInfCat.dual

end SemilatticeInfCat

/-- The equivalence between `SemilatticeSup` and `SemilatticeInf` induced by `order_dual` both ways.
-/
@[simps Functor inverse]
def semilatticeSupEquivSemilatticeInf : SemilatticeSupCat ≌ SemilatticeInfCat :=
  Equivalence.mk SemilatticeSupCat.dual SemilatticeInfCat.dual
    ((NatIso.ofComponents fun X => SemilatticeSupCat.Iso.mk <| OrderIso.dualDual X) fun X Y f =>
      rfl)
    ((NatIso.ofComponents fun X => SemilatticeInfCat.Iso.mk <| OrderIso.dualDual X) fun X Y f =>
      rfl)
#align SemilatticeSup_equiv_SemilatticeInf semilatticeSupEquivSemilatticeInf

theorem SemilatticeSup_dual_comp_forget_to_PartialOrder :
    SemilatticeSupCat.dual ⋙ forget₂ SemilatticeInfCat PartialOrderCat =
      forget₂ SemilatticeSupCat PartialOrderCat ⋙ PartialOrderCat.dual :=
  rfl
#align
  SemilatticeSup_dual_comp_forget_to_PartialOrder SemilatticeSup_dual_comp_forget_to_PartialOrder

theorem SemilatticeInf_dual_comp_forget_to_PartialOrder :
    SemilatticeInfCat.dual ⋙ forget₂ SemilatticeSupCat PartialOrderCat =
      forget₂ SemilatticeInfCat PartialOrderCat ⋙ PartialOrderCat.dual :=
  rfl
#align
  SemilatticeInf_dual_comp_forget_to_PartialOrder SemilatticeInf_dual_comp_forget_to_PartialOrder

