/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.category.DistLat
! leanprover-community/mathlib commit ce38d86c0b2d427ce208c3cee3159cb421d2b3c4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Category.Lat

/-!
# The category of distributive lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `DistLat`, the category of distributive lattices.

Note that [`DistLat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistLat` as we don't require bottom or top elements. Instead, this `DistLat`
corresponds to `BddDistLat`.
-/


universe u

open CategoryTheory

#print DistLatCat /-
/-- The category of distributive lattices. -/
def DistLatCat :=
  Bundled DistribLattice
#align DistLat DistLatCat
-/

namespace DistLatCat

instance : CoeSort DistLatCat (Type _) :=
  Bundled.hasCoeToSort

instance (X : DistLatCat) : DistribLattice X :=
  X.str

#print DistLatCat.of /-
/-- Construct a bundled `DistLat` from a `distrib_lattice` underlying type and typeclass. -/
def of (α : Type _) [DistribLattice α] : DistLatCat :=
  Bundled.of α
#align DistLat.of DistLatCat.of
-/

#print DistLatCat.coe_of /-
@[simp]
theorem coe_of (α : Type _) [DistribLattice α] : ↥(of α) = α :=
  rfl
#align DistLat.coe_of DistLatCat.coe_of
-/

instance : Inhabited DistLatCat :=
  ⟨of PUnit⟩

instance : BundledHom.ParentProjection @DistribLattice.toLattice :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for DistLatCat

/- warning: DistLat.has_forget_to_Lat -> DistLatCat.hasForgetToLatCat is a dubious translation:
lean 3 declaration is
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} DistLatCat.{u1} LatCat.{u1} DistLatCat.largeCategory.{u1} DistLatCat.concreteCategory.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.CategoryTheory.concreteCategory.{u1}
but is expected to have type
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} DistLatCat.{u1} LatCat.{u1} instDistLatCatLargeCategory.{u1} DistLatCat.instConcreteCategoryDistLatCatInstDistLatCatLargeCategory.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.instConcreteCategoryLatCatInstLargeCategoryLatCat.{u1}
Case conversion may be inaccurate. Consider using '#align DistLat.has_forget_to_Lat DistLatCat.hasForgetToLatCatₓ'. -/
instance hasForgetToLatCat : HasForget₂ DistLatCat LatCat :=
  BundledHom.forget₂ _ _
#align DistLat.has_forget_to_Lat DistLatCat.hasForgetToLatCat

/- warning: DistLat.iso.mk -> DistLatCat.Iso.mk is a dubious translation:
lean 3 declaration is
  forall {α : DistLatCat.{u1}} {β : DistLatCat.{u1}}, (OrderIso.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} α) (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} β) (Preorder.toHasLe.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} α) (PartialOrder.toPreorder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} α) (Lattice.toSemilatticeInf.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} α) (DistribLattice.toLattice.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} α) (DistLatCat.distribLattice.{u1} α)))))) (Preorder.toHasLe.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} β) (PartialOrder.toPreorder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} β) (Lattice.toSemilatticeInf.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} β) (DistribLattice.toLattice.{u1} (coeSort.{succ (succ u1), succ (succ u1)} DistLatCat.{u1} Type.{u1} DistLatCat.hasCoeToSort.{u1} β) (DistLatCat.distribLattice.{u1} β))))))) -> (CategoryTheory.Iso.{u1, succ u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1} α β)
but is expected to have type
  forall {α : DistLatCat.{u1}} {β : DistLatCat.{u1}}, (OrderIso.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} α) (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} β) (Preorder.toLE.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} α) (PartialOrder.toPreorder.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} α) (Lattice.toSemilatticeInf.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} α) (DistribLattice.toLattice.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} α) (DistLatCat.instDistribLatticeα.{u1} α)))))) (Preorder.toLE.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} β) (PartialOrder.toPreorder.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} β) (Lattice.toSemilatticeInf.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} β) (DistribLattice.toLattice.{u1} (CategoryTheory.Bundled.α.{u1, u1} DistribLattice.{u1} β) (DistLatCat.instDistribLatticeα.{u1} β))))))) -> (CategoryTheory.Iso.{u1, succ u1} DistLatCat.{u1} instDistLatCatLargeCategory.{u1} α β)
Case conversion may be inaccurate. Consider using '#align DistLat.iso.mk DistLatCat.Iso.mkₓ'. -/
/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps]
def Iso.mk {α β : DistLatCat.{u}} (e : α ≃o β) : α ≅ β
    where
  Hom := e
  inv := e.symm
  hom_inv_id' := by ext; exact e.symm_apply_apply _
  inv_hom_id' := by ext; exact e.apply_symm_apply _
#align DistLat.iso.mk DistLatCat.Iso.mk

/- warning: DistLat.dual -> DistLatCat.dual is a dubious translation:
lean 3 declaration is
  CategoryTheory.Functor.{u1, u1, succ u1, succ u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1}
but is expected to have type
  CategoryTheory.Functor.{u1, u1, succ u1, succ u1} DistLatCat.{u1} instDistLatCatLargeCategory.{u1} DistLatCat.{u1} instDistLatCatLargeCategory.{u1}
Case conversion may be inaccurate. Consider using '#align DistLat.dual DistLatCat.dualₓ'. -/
/-- `order_dual` as a functor. -/
@[simps]
def dual : DistLatCat ⥤ DistLatCat where
  obj X := of Xᵒᵈ
  map X Y := LatticeHom.dual
#align DistLat.dual DistLatCat.dual

/- warning: DistLat.dual_equiv -> DistLatCat.dualEquiv is a dubious translation:
lean 3 declaration is
  CategoryTheory.Equivalence.{u1, u1, succ u1, succ u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1}
but is expected to have type
  CategoryTheory.Equivalence.{u1, u1, succ u1, succ u1} DistLatCat.{u1} DistLatCat.{u1} instDistLatCatLargeCategory.{u1} instDistLatCatLargeCategory.{u1}
Case conversion may be inaccurate. Consider using '#align DistLat.dual_equiv DistLatCat.dualEquivₓ'. -/
/-- The equivalence between `DistLat` and itself induced by `order_dual` both ways. -/
@[simps Functor inverse]
def dualEquiv : DistLatCat ≌ DistLatCat :=
  Equivalence.mk dual dual
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
    (NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X) fun X Y f => rfl)
#align DistLat.dual_equiv DistLatCat.dualEquiv

end DistLatCat

/- warning: DistLat_dual_comp_forget_to_Lat -> distLatCat_dual_comp_forget_to_latCat is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1} LatCat.{u1} LatCat.CategoryTheory.largeCategory.{u1}) (CategoryTheory.Functor.comp.{u1, u1, u1, succ u1, succ u1, succ u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1} LatCat.{u1} LatCat.CategoryTheory.largeCategory.{u1} DistLatCat.dual.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} DistLatCat.{u1} LatCat.{u1} DistLatCat.largeCategory.{u1} DistLatCat.concreteCategory.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.CategoryTheory.concreteCategory.{u1} DistLatCat.hasForgetToLatCat.{u1})) (CategoryTheory.Functor.comp.{u1, u1, u1, succ u1, succ u1, succ u1} DistLatCat.{u1} DistLatCat.largeCategory.{u1} LatCat.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.{u1} LatCat.CategoryTheory.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} DistLatCat.{u1} LatCat.{u1} DistLatCat.largeCategory.{u1} DistLatCat.concreteCategory.{u1} LatCat.CategoryTheory.largeCategory.{u1} LatCat.CategoryTheory.concreteCategory.{u1} DistLatCat.hasForgetToLatCat.{u1}) LatCat.dual.{u1})
but is expected to have type
  Eq.{succ (succ u1)} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} DistLatCat.{u1} instDistLatCatLargeCategory.{u1} LatCat.{u1} LatCat.instLargeCategoryLatCat.{u1}) (CategoryTheory.Functor.comp.{u1, u1, u1, succ u1, succ u1, succ u1} DistLatCat.{u1} instDistLatCatLargeCategory.{u1} DistLatCat.{u1} instDistLatCatLargeCategory.{u1} LatCat.{u1} LatCat.instLargeCategoryLatCat.{u1} DistLatCat.dual.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} DistLatCat.{u1} LatCat.{u1} instDistLatCatLargeCategory.{u1} DistLatCat.instConcreteCategoryDistLatCatInstDistLatCatLargeCategory.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.instConcreteCategoryLatCatInstLargeCategoryLatCat.{u1} DistLatCat.hasForgetToLatCat.{u1})) (CategoryTheory.Functor.comp.{u1, u1, u1, succ u1, succ u1, succ u1} DistLatCat.{u1} instDistLatCatLargeCategory.{u1} LatCat.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.{u1} LatCat.instLargeCategoryLatCat.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} DistLatCat.{u1} LatCat.{u1} instDistLatCatLargeCategory.{u1} DistLatCat.instConcreteCategoryDistLatCatInstDistLatCatLargeCategory.{u1} LatCat.instLargeCategoryLatCat.{u1} LatCat.instConcreteCategoryLatCatInstLargeCategoryLatCat.{u1} DistLatCat.hasForgetToLatCat.{u1}) LatCat.dual.{u1})
Case conversion may be inaccurate. Consider using '#align DistLat_dual_comp_forget_to_Lat distLatCat_dual_comp_forget_to_latCatₓ'. -/
theorem distLatCat_dual_comp_forget_to_latCat :
    DistLatCat.dual ⋙ forget₂ DistLatCat LatCat = forget₂ DistLatCat LatCat ⋙ LatCat.dual :=
  rfl
#align DistLat_dual_comp_forget_to_Lat distLatCat_dual_comp_forget_to_latCat

