/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Category.Group.Preadditive
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.Algebra.Category.Group.Limits

/-!
# The category of abelian groups has finite biproducts
-/


open CategoryTheory

open CategoryTheory.Limits

open BigOperators

universe u

namespace AddCommGroupₓₓ

-- As `AddCommGroup` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts AddCommGroupₓₓ :=
  has_binary_biproducts.of_has_binary_products

instance : HasFiniteBiproducts AddCommGroupₓₓ :=
  has_finite_biproducts.of_has_finite_products

/-- Construct limit data for a binary product in `AddCommGroup`, using `AddCommGroup.of (G × H)`.
-/
-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
@[simps cone_X is_limit_lift]
def binaryProductLimitCone (G H : AddCommGroupₓₓ.{u}) : Limits.LimitCone (pair G H) where
  Cone :=
    { x := AddCommGroupₓₓ.of (G × H),
      π := { app := fun j => WalkingPair.casesOn j (AddMonoidHom.fst G H) (AddMonoidHom.snd G H) } }
  IsLimit :=
    { lift := fun s => AddMonoidHom.prod (s.π.app WalkingPair.left) (s.π.app WalkingPair.right),
      fac' := by
        rintro s (⟨⟩ | ⟨⟩) <;>
          · ext x
            simp
            ,
      uniq' := fun s m w => by
        ext <;> [rw [← w walking_pair.left], rw [← w walking_pair.right]] <;> rfl }

@[simp]
theorem binary_product_limit_cone_cone_π_app_left (G H : AddCommGroupₓₓ.{u}) :
    (binaryProductLimitCone G H).Cone.π.app WalkingPair.left = AddMonoidHom.fst G H :=
  rfl

@[simp]
theorem binary_product_limit_cone_cone_π_app_right (G H : AddCommGroupₓₓ.{u}) :
    (binaryProductLimitCone G H).Cone.π.app WalkingPair.right = AddMonoidHom.snd G H :=
  rfl

/-- We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
@[simps]
noncomputable def biprodIsoProd (G H : AddCommGroupₓₓ.{u}) : (G ⊞ H : AddCommGroupₓₓ) ≅ AddCommGroupₓₓ.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).IsLimit

-- Furthermore, our biproduct will automatically function as a coproduct.
example (G H : AddCommGroupₓₓ.{u}) : HasColimit (pair G H) := by
  infer_instance

variable {J : Type u} (F : Discrete J ⥤ AddCommGroupₓₓ.{u})

namespace HasLimit

/-- The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
def lift (s : Cone F) : s.x ⟶ AddCommGroupₓₓ.of (∀ j, F.obj j) where
  toFun := fun x j => s.π.app j x
  map_zero' := by
    ext
    simp
  map_add' := fun x y => by
    ext
    simp

@[simp]
theorem lift_apply (s : Cone F) (x : s.x) (j : J) : (lift F s) x j = s.π.app j x :=
  rfl

/-- Construct limit data for a product in `AddCommGroup`, using `AddCommGroup.of (Π j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone F where
  Cone :=
    { x := AddCommGroupₓₓ.of (∀ j, F.obj j), π := Discrete.natTrans fun j => Pi.evalAddMonoidHom (fun j => F.obj j) j }
  IsLimit :=
    { lift := lift F,
      fac' := fun s j => by
        ext
        simp ,
      uniq' := fun s m w => by
        ext x j
        dsimp' only [has_limit.lift]
        simp only [AddMonoidHom.coe_mk]
        exact congr_argₓ (fun f : s.X ⟶ F.obj j => (f : s.X → F.obj j) x) (w j) }

end HasLimit

open HasLimit

/-- We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
@[simps hom_apply]
noncomputable def biproductIsoPi [DecidableEq J] [Fintype J] (f : J → AddCommGroupₓₓ.{u}) :
    (⨁ f : AddCommGroupₓₓ) ≅ AddCommGroupₓₓ.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (Biproduct.isLimit f) (productLimitCone (Discrete.functor f)).IsLimit

@[simp, elementwise]
theorem biproduct_iso_pi_inv_comp_π [DecidableEq J] [Fintype J] (f : J → AddCommGroupₓₓ.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = Pi.evalAddMonoidHom (fun j => f j) j :=
  IsLimit.cone_point_unique_up_to_iso_inv_comp _ _ _

end AddCommGroupₓₓ

