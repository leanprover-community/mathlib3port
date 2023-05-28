/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Group.biproducts
! leanprover-community/mathlib commit 234ddfeaa5572bc13716dd215c6444410a679a8e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Category.Group.Preadditive
import Mathbin.CategoryTheory.Preadditive.Biproducts
import Mathbin.Algebra.Category.Group.Limits

/-!
# The category of abelian groups has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

open BigOperators

universe w u

namespace AddCommGroupCat

-- As `AddCommGroup` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts AddCommGroupCat :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance : HasFiniteBiproducts AddCommGroupCat :=
  HasFiniteBiproducts.of_hasFiniteProducts

#print AddCommGroupCat.binaryProductLimitCone /-
-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `AddCommGroup`, using `AddCommGroup.of (G × H)`.
-/
@[simps cone_x isLimit_lift]
def binaryProductLimitCone (G H : AddCommGroupCat.{u}) : Limits.LimitCone (pair G H)
    where
  Cone :=
    { pt := AddCommGroupCat.of (G × H)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (AddMonoidHom.fst G H) (AddMonoidHom.snd G H)
          naturality' := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  IsLimit :=
    { lift := fun s => AddMonoidHom.prod (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩)
      fac := by
        rintro s (⟨⟩ | ⟨⟩) <;>
          · ext x
            simp
      uniq := fun s m w => by
        ext <;> [rw [← w ⟨walking_pair.left⟩];rw [← w ⟨walking_pair.right⟩]] <;> rfl }
#align AddCommGroup.binary_product_limit_cone AddCommGroupCat.binaryProductLimitCone
-/

/- warning: AddCommGroup.binary_product_limit_cone_cone_π_app_left -> AddCommGroupCat.binaryProductLimitCone_cone_π_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align AddCommGroup.binary_product_limit_cone_cone_π_app_left AddCommGroupCat.binaryProductLimitCone_cone_π_app_leftₓ'. -/
@[simp]
theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGroupCat.{u}) :
    (binaryProductLimitCone G H).Cone.π.app ⟨WalkingPair.left⟩ = AddMonoidHom.fst G H :=
  rfl
#align AddCommGroup.binary_product_limit_cone_cone_π_app_left AddCommGroupCat.binaryProductLimitCone_cone_π_app_left

/- warning: AddCommGroup.binary_product_limit_cone_cone_π_app_right -> AddCommGroupCat.binaryProductLimitCone_cone_π_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align AddCommGroup.binary_product_limit_cone_cone_π_app_right AddCommGroupCat.binaryProductLimitCone_cone_π_app_rightₓ'. -/
@[simp]
theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGroupCat.{u}) :
    (binaryProductLimitCone G H).Cone.π.app ⟨WalkingPair.right⟩ = AddMonoidHom.snd G H :=
  rfl
#align AddCommGroup.binary_product_limit_cone_cone_π_app_right AddCommGroupCat.binaryProductLimitCone_cone_π_app_right

/- warning: AddCommGroup.biprod_iso_prod -> AddCommGroupCat.biprodIsoProd is a dubious translation:
lean 3 declaration is
  forall (G : AddCommGroupCat.{u1}) (H : AddCommGroupCat.{u1}), CategoryTheory.Iso.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Limits.biprod.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.CategoryTheory.preadditive.{u1}) G H (AddCommGroupCat.biprodIsoProd._proof_1.{u1} G H)) (AddCommGroupCat.of.{u1} (Prod.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} G) (coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} H)) (Prod.addCommGroup.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} G) (coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} H) (AddCommGroupCat.addCommGroupInstance.{u1} G) (AddCommGroupCat.addCommGroupInstance.{u1} H)))
but is expected to have type
  forall (G : AddCommGroupCat.{u1}) (H : AddCommGroupCat.{u1}), CategoryTheory.Iso.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Limits.biprod.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) G H (CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) AddCommGroupCat.instHasBinaryBiproductsAddCommGroupCatInstAddCommGroupCatLargeCategoryPreadditiveHasZeroMorphismsInstPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1} G H)) (AddCommGroupCat.of.{u1} (Prod.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} G) (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H)) (Prod.instAddCommGroupSum.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} G) (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroupCat.addCommGroupInstance.{u1} G) (AddCommGroupCat.addCommGroupInstance.{u1} H)))
Case conversion may be inaccurate. Consider using '#align AddCommGroup.biprod_iso_prod AddCommGroupCat.biprodIsoProdₓ'. -/
/-- We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
@[simps hom_apply]
noncomputable def biprodIsoProd (G H : AddCommGroupCat.{u}) :
    (G ⊞ H : AddCommGroupCat) ≅ AddCommGroupCat.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).IsLimit
#align AddCommGroup.biprod_iso_prod AddCommGroupCat.biprodIsoProd

/- warning: AddCommGroup.biprod_iso_prod_inv_comp_fst -> AddCommGroupCat.biprodIsoProd_inv_comp_fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align AddCommGroup.biprod_iso_prod_inv_comp_fst AddCommGroupCat.biprodIsoProd_inv_comp_fstₓ'. -/
@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (G H : AddCommGroupCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = AddMonoidHom.fst G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)
#align AddCommGroup.biprod_iso_prod_inv_comp_fst AddCommGroupCat.biprodIsoProd_inv_comp_fst

/- warning: AddCommGroup.biprod_iso_prod_inv_comp_snd -> AddCommGroupCat.biprodIsoProd_inv_comp_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align AddCommGroup.biprod_iso_prod_inv_comp_snd AddCommGroupCat.biprodIsoProd_inv_comp_sndₓ'. -/
@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (G H : AddCommGroupCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = AddMonoidHom.snd G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)
#align AddCommGroup.biprod_iso_prod_inv_comp_snd AddCommGroupCat.biprodIsoProd_inv_comp_snd

namespace HasLimit

variable {J : Type w} (f : J → AddCommGroupCat.{max w u})

#print AddCommGroupCat.HasLimit.lift /-
/-- The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
@[simps]
def lift (s : Fan f) : s.pt ⟶ AddCommGroupCat.of (∀ j, f j)
    where
  toFun x j := s.π.app ⟨j⟩ x
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp
#align AddCommGroup.has_limit.lift AddCommGroupCat.HasLimit.lift
-/

#print AddCommGroupCat.HasLimit.productLimitCone /-
/-- Construct limit data for a product in `AddCommGroup`, using `AddCommGroup.of (Π j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f)
    where
  Cone :=
    { pt := AddCommGroupCat.of (∀ j, f j)
      π := Discrete.natTrans fun j => Pi.evalAddMonoidHom (fun j => f j) j.as }
  IsLimit :=
    { lift := lift f
      fac := fun s j => by
        cases j
        ext
        simp
      uniq := fun s m w => by
        ext (x j)
        dsimp only [has_limit.lift]
        simp only [AddMonoidHom.coe_mk]
        exact congr_arg (fun g : s.X ⟶ f j => (g : s.X → f j) x) (w ⟨j⟩) }
#align AddCommGroup.has_limit.product_limit_cone AddCommGroupCat.HasLimit.productLimitCone
-/

end HasLimit

open HasLimit

variable {J : Type} [Fintype J]

/- warning: AddCommGroup.biproduct_iso_pi -> AddCommGroupCat.biproductIsoPi is a dubious translation:
lean 3 declaration is
  forall {J : Type} [_inst_1 : Fintype.{0} J] (f : J -> AddCommGroupCat.{u1}), CategoryTheory.Iso.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Limits.biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.CategoryTheory.preadditive.{u1}) f (AddCommGroupCat.biproductIsoPi._proof_1.{u1} J _inst_1 f)) (AddCommGroupCat.of.{u1} (forall (j : J), coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i))))
but is expected to have type
  forall {J : Type} [_inst_1 : Fintype.{0} J] (f : J -> AddCommGroupCat.{u1}), CategoryTheory.Iso.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Limits.biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) f (CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Limits.hasBiproductsOfShape_finite.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) AddCommGroupCat.instHasFiniteBiproductsAddCommGroupCatInstAddCommGroupCatLargeCategoryPreadditiveHasZeroMorphismsInstPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1} (Finite.of_fintype.{0} J _inst_1)) f)) (AddCommGroupCat.of.{u1} (forall (j : J), CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i))))
Case conversion may be inaccurate. Consider using '#align AddCommGroup.biproduct_iso_pi AddCommGroupCat.biproductIsoPiₓ'. -/
/-- We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
@[simps hom_apply]
noncomputable def biproductIsoPi (f : J → AddCommGroupCat.{u}) :
    (⨁ f : AddCommGroupCat) ≅ AddCommGroupCat.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).IsLimit
#align AddCommGroup.biproduct_iso_pi AddCommGroupCat.biproductIsoPi

/- warning: AddCommGroup.biproduct_iso_pi_inv_comp_π -> AddCommGroupCat.biproductIsoPi_inv_comp_π is a dubious translation:
lean 3 declaration is
  forall {J : Type} [_inst_1 : Fintype.{0} J] (f : J -> AddCommGroupCat.{u1}) (j : J), Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1})) (AddCommGroupCat.of.{u1} (forall (j : J), coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i)))) (f j)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (AddCommGroupCat.of.{u1} (forall (j : J), coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i)))) (CategoryTheory.Limits.biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.CategoryTheory.preadditive.{u1}) f (AddCommGroupCat.biproductIsoPi._proof_1.{u1} J _inst_1 f)) (f j) (CategoryTheory.Iso.inv.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Limits.biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.CategoryTheory.preadditive.{u1}) f (AddCommGroupCat.biproductIsoPi._proof_1.{u1} J _inst_1 f)) (AddCommGroupCat.of.{u1} (forall (j : J), coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i)))) (AddCommGroupCat.biproductIsoPi.{u1} J _inst_1 f)) (CategoryTheory.Limits.biproduct.π.{0, u1, succ u1} J AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.CategoryTheory.preadditive.{u1}) f (AddCommGroupCat.biproductIsoPi._proof_1.{u1} J _inst_1 f) j)) (Pi.evalAddMonoidHom.{0, u1} J (fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) (fun (_x : J) => AddMonoid.toAddZeroClass.{u1} ((fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) _x) (SubNegMonoid.toAddMonoid.{u1} ((fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) _x) (AddGroup.toSubNegMonoid.{u1} ((fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) _x) (AddCommGroup.toAddGroup.{u1} ((fun (j : J) => coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (f j)) _x) ((fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i)) _x))))) j)
but is expected to have type
  forall {J : Type} [_inst_1 : Fintype.{0} J] (f : J -> AddCommGroupCat.{u1}) (j : J), Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (AddCommGroupCat.of.{u1} (forall (j : J), CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i)))) (f j)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (AddCommGroupCat.of.{u1} (forall (j : J), CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i)))) (CategoryTheory.Limits.biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) f (CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Limits.hasBiproductsOfShape_finite.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) AddCommGroupCat.instHasFiniteBiproductsAddCommGroupCatInstAddCommGroupCatLargeCategoryPreadditiveHasZeroMorphismsInstPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1} (Finite.of_fintype.{0} J _inst_1)) f)) (f j) (CategoryTheory.Iso.inv.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Limits.biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) f (CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Limits.hasBiproductsOfShape_finite.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) AddCommGroupCat.instHasFiniteBiproductsAddCommGroupCatInstAddCommGroupCatLargeCategoryPreadditiveHasZeroMorphismsInstPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1} (Finite.of_fintype.{0} J _inst_1)) f)) (AddCommGroupCat.of.{u1} (forall (j : J), CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (fun (i : J) => AddCommGroupCat.addCommGroupInstance.{u1} (f i)))) (AddCommGroupCat.biproductIsoPi.{u1} J _inst_1 f)) (CategoryTheory.Limits.biproduct.π.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) f (CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Limits.hasBiproductsOfShape_finite.{0, u1, succ u1} J AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) AddCommGroupCat.instHasFiniteBiproductsAddCommGroupCatInstAddCommGroupCatLargeCategoryPreadditiveHasZeroMorphismsInstPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1} (Finite.of_fintype.{0} J _inst_1)) f) j)) (Pi.evalAddMonoidHom.{0, u1} J (fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) (fun (_x : J) => AddMonoid.toAddZeroClass.{u1} ((fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) _x) (SubNegMonoid.toAddMonoid.{u1} ((fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) _x) (AddGroup.toSubNegMonoid.{u1} ((fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) _x) (AddCommGroup.toAddGroup.{u1} ((fun (j : J) => CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (f j)) _x) (AddCommGroupCat.addCommGroupInstance.{u1} (f _x)))))) j)
Case conversion may be inaccurate. Consider using '#align AddCommGroup.biproduct_iso_pi_inv_comp_π AddCommGroupCat.biproductIsoPi_inv_comp_πₓ'. -/
@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π (f : J → AddCommGroupCat.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = Pi.evalAddMonoidHom (fun j => f j) j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)
#align AddCommGroup.biproduct_iso_pi_inv_comp_π AddCommGroupCat.biproductIsoPi_inv_comp_π

end AddCommGroupCat

