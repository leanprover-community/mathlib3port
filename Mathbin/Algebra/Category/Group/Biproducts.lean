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

/-- Construct limit data for a binary product in `AddCommGroup`, using `AddCommGroup.of (G × H)`.
-/
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

instance has_binary_product (G H : AddCommGroupₓₓ.{u}) : HasBinaryProduct G H :=
  HasLimit.mk (binaryProductLimitCone G H)

instance (G H : AddCommGroupₓₓ.{u}) : HasBinaryBiproduct G H :=
  HasBinaryBiproduct.of_has_binary_product _ _

/-- We verify that the biproduct in AddCommGroup is isomorphic to
the cartesian product of the underlying types:
-/
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

section

open HasLimit

variable [DecidableEq J] [Fintype J]

instance (f : J → AddCommGroupₓₓ.{u}) : HasBiproduct f :=
  HasBiproduct.of_has_product _

/-- We verify that the biproduct we've just defined is isomorphic to the AddCommGroup structure
on the dependent function type
-/
noncomputable def biproductIsoPi (f : J → AddCommGroupₓₓ.{u}) : (⨁ f : AddCommGroupₓₓ) ≅ AddCommGroupₓₓ.of (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (Biproduct.isLimit f) (productLimitCone (Discrete.functor f)).IsLimit

end

instance : HasFiniteBiproducts AddCommGroupₓₓ :=
  ⟨fun J _ _ =>
    { HasBiproduct := fun f => by
        infer_instance }⟩

end AddCommGroupₓₓ

