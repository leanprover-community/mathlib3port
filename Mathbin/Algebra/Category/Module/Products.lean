/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.LinearAlgebra.Pi
import Mathbin.Algebra.Category.Module.Basic

#align_import algebra.category.Module.products from "leanprover-community/mathlib"@"86d1873c01a723aba6788f0b9051ae3d23b4c1c3"

/-!
# The concrete products in the category of modules are products in the categorical sense.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

#print ModuleCat.productCone /-
/-- The product cone induced by the concrete product. -/
def productCone : Fan Z :=
  Fan.mk (ModuleCat.of R (∀ i : ι, Z i)) fun i => (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i)
#align Module.product_cone ModuleCat.productCone
-/

#print ModuleCat.productConeIsLimit /-
/-- The concrete product cone is limiting. -/
def productConeIsLimit : IsLimit (productCone Z)
    where
  lift s := (LinearMap.pi fun j => s.π.app ⟨j⟩ : s.pt →ₗ[R] ∀ i : ι, Z i)
  fac s j := by cases j; tidy
  uniq s m w := by ext x i; exact LinearMap.congr_fun (w ⟨i⟩) x
#align Module.product_cone_is_limit ModuleCat.productConeIsLimit
-/

-- While we could use this to construct a `has_products (Module R)` instance,
-- we already have `has_limits (Module R)` in `algebra.category.Module.limits`.
variable [HasProduct Z]

#print ModuleCat.piIsoPi /-
/-- The categorical product of a family of objects in `Module`
agrees with the usual module-theoretical product.
-/
noncomputable def piIsoPi : ∏ Z ≅ ModuleCat.of R (∀ i, Z i) :=
  limit.isoLimitCone ⟨_, productConeIsLimit Z⟩
#align Module.pi_iso_pi ModuleCat.piIsoPi
-/

#print ModuleCat.piIsoPi_inv_kernel_ι /-
-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
theorem piIsoPi_inv_kernel_ι (i : ι) :
    (piIsoPi Z).inv ≫ Pi.π Z i = (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) :=
  limit.isoLimitCone_inv_π _ _
#align Module.pi_iso_pi_inv_kernel_ι ModuleCat.piIsoPi_inv_kernel_ι
-/

#print ModuleCat.piIsoPi_hom_ker_subtype /-
@[simp, elementwise]
theorem piIsoPi_hom_ker_subtype (i : ι) :
    (piIsoPi Z).hom ≫ (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) = Pi.π Z i :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)
#align Module.pi_iso_pi_hom_ker_subtype ModuleCat.piIsoPi_hom_ker_subtype
-/

end ModuleCat

