/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.Category.PartOrd
import Order.Hom.Lattice

#align_import order.category.Semilat from "leanprover-community/mathlib"@"d07a9c875ed7139abfde6a333b2be205c5bd404e"

/-!
# The categories of semilattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `SemilatSup` and `SemilatInf`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/


universe u

open CategoryTheory

#print SemilatSupCat /-
/-- The category of sup-semilattices with a bottom element. -/
structure SemilatSupCat : Type (u + 1) where
  pt : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot X]
#align SemilatSup SemilatSupCat
-/

#print SemilatInfCat /-
/-- The category of inf-semilattices with a top element. -/
structure SemilatInfCat : Type (u + 1) where
  pt : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop X]
#align SemilatInf SemilatInfCat
-/

attribute [protected] SemilatSupCat.X SemilatInfCat.X

namespace SemilatSupCat

instance : CoeSort SemilatSupCat (Type _) :=
  ⟨SemilatSupCat.X⟩

attribute [instance] is_semilattice_sup is_order_bot

#print SemilatSupCat.of /-
/-- Construct a bundled `SemilatSup` from a `semilattice_sup`. -/
def of (α : Type _) [SemilatticeSup α] [OrderBot α] : SemilatSupCat :=
  ⟨α⟩
#align SemilatSup.of SemilatSupCat.of
-/

#print SemilatSupCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl
#align SemilatSup.coe_of SemilatSupCat.coe_of
-/

instance : Inhabited SemilatSupCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatSupCat
    where
  Hom X Y := SupBotHom X Y
  id X := SupBotHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := SupBotHom.comp_id
  comp_id' X Y := SupBotHom.id_comp
  assoc' W X Y Z _ _ _ := SupBotHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatSupCat
    where
  forget :=
    { obj := SemilatSupCat.X
      map := fun X Y => coeFn }
  forget_faithful := ⟨fun X Y => DFunLike.coe_injective⟩

#print SemilatSupCat.hasForgetToPartOrd /-
instance hasForgetToPartOrd : HasForget₂ SemilatSupCat PartOrd
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
#align SemilatSup.has_forget_to_PartOrd SemilatSupCat.hasForgetToPartOrd
-/

#print SemilatSupCat.coe_forget_to_partOrd /-
@[simp]
theorem coe_forget_to_partOrd (X : SemilatSupCat) : ↥((forget₂ SemilatSupCat PartOrd).obj X) = ↥X :=
  rfl
#align SemilatSup.coe_forget_to_PartOrd SemilatSupCat.coe_forget_to_partOrd
-/

end SemilatSupCat

namespace SemilatInfCat

instance : CoeSort SemilatInfCat (Type _) :=
  ⟨SemilatInfCat.X⟩

attribute [instance] is_semilattice_inf is_order_top

#print SemilatInfCat.of /-
/-- Construct a bundled `SemilatInf` from a `semilattice_inf`. -/
def of (α : Type _) [SemilatticeInf α] [OrderTop α] : SemilatInfCat :=
  ⟨α⟩
#align SemilatInf.of SemilatInfCat.of
-/

#print SemilatInfCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl
#align SemilatInf.coe_of SemilatInfCat.coe_of
-/

instance : Inhabited SemilatInfCat :=
  ⟨of PUnit⟩

instance : LargeCategory.{u} SemilatInfCat
    where
  Hom X Y := InfTopHom X Y
  id X := InfTopHom.id X
  comp X Y Z f g := g.comp f
  id_comp' X Y := InfTopHom.comp_id
  comp_id' X Y := InfTopHom.id_comp
  assoc' W X Y Z _ _ _ := InfTopHom.comp_assoc _ _ _

instance : ConcreteCategory SemilatInfCat
    where
  forget :=
    { obj := SemilatInfCat.X
      map := fun X Y => coeFn }
  forget_faithful := ⟨fun X Y => DFunLike.coe_injective⟩

#print SemilatInfCat.hasForgetToPartOrd /-
instance hasForgetToPartOrd : HasForget₂ SemilatInfCat PartOrd
    where forget₂ :=
    { obj := fun X => ⟨X⟩
      map := fun X Y f => f }
#align SemilatInf.has_forget_to_PartOrd SemilatInfCat.hasForgetToPartOrd
-/

#print SemilatInfCat.coe_forget_to_partOrd /-
@[simp]
theorem coe_forget_to_partOrd (X : SemilatInfCat) : ↥((forget₂ SemilatInfCat PartOrd).obj X) = ↥X :=
  rfl
#align SemilatInf.coe_forget_to_PartOrd SemilatInfCat.coe_forget_to_partOrd
-/

end SemilatInfCat

/-! ### Order dual -/


namespace SemilatSupCat

#print SemilatSupCat.Iso.mk /-
/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatSupCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align SemilatSup.iso.mk SemilatSupCat.Iso.mk
-/

#print SemilatSupCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : SemilatSupCat ⥤ SemilatInfCat
    where
  obj X := SemilatInfCat.of Xᵒᵈ
  map X Y := SupBotHom.dual
#align SemilatSup.dual SemilatSupCat.dual
-/

end SemilatSupCat

namespace SemilatInfCat

#print SemilatInfCat.Iso.mk /-
/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : SemilatInfCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align SemilatInf.iso.mk SemilatInfCat.Iso.mk
-/

#print SemilatInfCat.dual /-
/-- `order_dual` as a functor. -/
@[simps]
def dual : SemilatInfCat ⥤ SemilatSupCat
    where
  obj X := SemilatSupCat.of Xᵒᵈ
  map X Y := InfTopHom.dual
#align SemilatInf.dual SemilatInfCat.dual
-/

end SemilatInfCat

#print SemilatSupCatEquivSemilatInfCat /-
/-- The equivalence between `SemilatSup` and `SemilatInf` induced by `order_dual` both ways.
-/
@[simps Functor inverse]
def SemilatSupCatEquivSemilatInfCat : SemilatSupCat ≌ SemilatInfCat :=
  Equivalence.mk SemilatSupCat.dual SemilatInfCat.dual
    (NatIso.ofComponents (fun X => SemilatSupCat.Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => SemilatInfCat.Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align SemilatSup_equiv_SemilatInf SemilatSupCatEquivSemilatInfCat
-/

#print SemilatSupCat_dual_comp_forget_to_partOrd /-
theorem SemilatSupCat_dual_comp_forget_to_partOrd :
    SemilatSupCat.dual ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ SemilatSupCat PartOrd ⋙ PartOrd.dual :=
  rfl
#align SemilatSup_dual_comp_forget_to_PartOrd SemilatSupCat_dual_comp_forget_to_partOrd
-/

#print SemilatInfCat_dual_comp_forget_to_partOrd /-
theorem SemilatInfCat_dual_comp_forget_to_partOrd :
    SemilatInfCat.dual ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ SemilatInfCat PartOrd ⋙ PartOrd.dual :=
  rfl
#align SemilatInf_dual_comp_forget_to_PartOrd SemilatInfCat_dual_comp_forget_to_partOrd
-/

