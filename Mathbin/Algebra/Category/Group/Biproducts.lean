/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Algebra.Group.Pi
import Algebra.Category.Group.Preadditive
import CategoryTheory.Preadditive.Biproducts
import Algebra.Category.Group.Limits

#align_import algebra.category.Group.biproducts from "leanprover-community/mathlib"@"f60c6087a7275b72d5db3c5a1d0e19e35a429c0a"

/-!
# The category of abelian groups has finite biproducts

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

open CategoryTheory.Limits

open scoped BigOperators

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
      fac := by rintro s (⟨⟩ | ⟨⟩) <;> · ext x; simp
      uniq := fun s m w => by
        ext <;> [rw [← w ⟨walking_pair.left⟩]; rw [← w ⟨walking_pair.right⟩]] <;> rfl }
#align AddCommGroup.binary_product_limit_cone AddCommGroupCat.binaryProductLimitCone
-/

#print AddCommGroupCat.binaryProductLimitCone_cone_π_app_left /-
@[simp]
theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGroupCat.{u}) :
    (binaryProductLimitCone G H).Cone.π.app ⟨WalkingPair.left⟩ = AddMonoidHom.fst G H :=
  rfl
#align AddCommGroup.binary_product_limit_cone_cone_π_app_left AddCommGroupCat.binaryProductLimitCone_cone_π_app_left
-/

#print AddCommGroupCat.binaryProductLimitCone_cone_π_app_right /-
@[simp]
theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGroupCat.{u}) :
    (binaryProductLimitCone G H).Cone.π.app ⟨WalkingPair.right⟩ = AddMonoidHom.snd G H :=
  rfl
#align AddCommGroup.binary_product_limit_cone_cone_π_app_right AddCommGroupCat.binaryProductLimitCone_cone_π_app_right
-/

#print AddCommGroupCat.biprodIsoProd /-
/-- We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
@[simps hom_apply]
noncomputable def biprodIsoProd (G H : AddCommGroupCat.{u}) :
    (G ⊞ H : AddCommGroupCat) ≅ AddCommGroupCat.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).IsLimit
#align AddCommGroup.biprod_iso_prod AddCommGroupCat.biprodIsoProd
-/

#print AddCommGroupCat.biprodIsoProd_inv_comp_fst /-
@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (G H : AddCommGroupCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = AddMonoidHom.fst G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)
#align AddCommGroup.biprod_iso_prod_inv_comp_fst AddCommGroupCat.biprodIsoProd_inv_comp_fst
-/

#print AddCommGroupCat.biprodIsoProd_inv_comp_snd /-
@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (G H : AddCommGroupCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = AddMonoidHom.snd G H :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)
#align AddCommGroup.biprod_iso_prod_inv_comp_snd AddCommGroupCat.biprodIsoProd_inv_comp_snd
-/

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
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
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
      fac := fun s j => by cases j; ext; simp
      uniq := fun s m w => by
        ext x j
        dsimp only [has_limit.lift]
        simp only [AddMonoidHom.coe_mk]
        exact congr_arg (fun g : s.X ⟶ f j => (g : s.X → f j) x) (w ⟨j⟩) }
#align AddCommGroup.has_limit.product_limit_cone AddCommGroupCat.HasLimit.productLimitCone
-/

end HasLimit

open HasLimit

variable {J : Type} [Fintype J]

#print AddCommGroupCat.biproductIsoPi /-
/-- We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
@[simps hom_apply]
noncomputable def biproductIsoPi (f : J → AddCommGroupCat.{u}) :
    (⨁ f : AddCommGroupCat) ≅ AddCommGroupCat.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).IsLimit
#align AddCommGroup.biproduct_iso_pi AddCommGroupCat.biproductIsoPi
-/

#print AddCommGroupCat.biproductIsoPi_inv_comp_π /-
@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π (f : J → AddCommGroupCat.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = Pi.evalAddMonoidHom (fun j => f j) j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)
#align AddCommGroup.biproduct_iso_pi_inv_comp_π AddCommGroupCat.biproductIsoPi_inv_comp_π
-/

end AddCommGroupCat

