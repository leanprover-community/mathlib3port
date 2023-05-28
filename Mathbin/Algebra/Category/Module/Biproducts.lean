/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.biproducts
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.Algebra.Homology.ShortExact.Abelian

/-!
# The category of `R`-modules has finite biproducts

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

open CategoryTheory.Limits

open BigOperators

universe w v u

namespace ModuleCat

variable {R : Type u} [Ring R]

-- As `Module R` is preadditive, and has all limits, it automatically has biproducts.
instance : HasBinaryBiproducts (ModuleCat.{v} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

instance : HasFiniteBiproducts (ModuleCat.{v} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

#print ModuleCat.binaryProductLimitCone /-
-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `Module R`, using `Module.of R (M × N)`.
-/
@[simps cone_x isLimit_lift]
def binaryProductLimitCone (M N : ModuleCat.{v} R) : Limits.LimitCone (pair M N)
    where
  Cone :=
    { pt := ModuleCat.of R (M × N)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (LinearMap.fst R M N) (LinearMap.snd R M N)
          naturality' := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  IsLimit :=
    { lift := fun s => LinearMap.prod (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩)
      fac := by
        rintro s (⟨⟩ | ⟨⟩) <;>
          · ext x;
            simp only [binary_fan.π_app_right, binary_fan.π_app_left, ModuleCat.coe_comp,
              Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.prod_apply,
              Pi.prod]
      uniq := fun s m w => by
        ext <;> [rw [← w ⟨walking_pair.left⟩];rw [← w ⟨walking_pair.right⟩]] <;> rfl }
#align Module.binary_product_limit_cone ModuleCat.binaryProductLimitCone
-/

/- warning: Module.binary_product_limit_cone_cone_π_app_left -> ModuleCat.binaryProductLimitCone_cone_π_app_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.binary_product_limit_cone_cone_π_app_left ModuleCat.binaryProductLimitCone_cone_π_app_leftₓ'. -/
@[simp]
theorem binaryProductLimitCone_cone_π_app_left (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).Cone.π.app ⟨WalkingPair.left⟩ = LinearMap.fst R M N :=
  rfl
#align Module.binary_product_limit_cone_cone_π_app_left ModuleCat.binaryProductLimitCone_cone_π_app_left

/- warning: Module.binary_product_limit_cone_cone_π_app_right -> ModuleCat.binaryProductLimitCone_cone_π_app_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.binary_product_limit_cone_cone_π_app_right ModuleCat.binaryProductLimitCone_cone_π_app_rightₓ'. -/
@[simp]
theorem binaryProductLimitCone_cone_π_app_right (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).Cone.π.app ⟨WalkingPair.right⟩ = LinearMap.snd R M N :=
  rfl
#align Module.binary_product_limit_cone_cone_π_app_right ModuleCat.binaryProductLimitCone_cone_π_app_right

/- warning: Module.biprod_iso_prod -> ModuleCat.biprodIsoProd is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] (M : ModuleCat.{u1, u2} R _inst_1) (N : ModuleCat.{u1, u2} R _inst_1), CategoryTheory.Iso.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Limits.biprod.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.CategoryTheory.preadditive.{u1, u2} R _inst_1)) M N (ModuleCat.biprodIsoProd._proof_1.{u2, u1} R _inst_1 M N)) (ModuleCat.of.{u1, u2} R _inst_1 (Prod.{u1, u1} (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) M) (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) N)) (Prod.addCommGroup.{u1, u1} (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) M) (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) N) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 M) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 N)) (Prod.module.{u2, u1, u1} R (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) M) (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) N) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) M) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 M)) (AddCommGroup.toAddCommMonoid.{u1} (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) N) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 N)) (ModuleCat.isModule.{u1, u2} R _inst_1 M) (ModuleCat.isModule.{u1, u2} R _inst_1 N)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] (M : ModuleCat.{u1, u2} R _inst_1) (N : ModuleCat.{u1, u2} R _inst_1), CategoryTheory.Iso.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Limits.biprod.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.instPreadditiveModuleCatModuleCategory.{u1, u2} R _inst_1)) M N (CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.instPreadditiveModuleCatModuleCategory.{u1, u2} R _inst_1)) (ModuleCat.instHasBinaryBiproductsModuleCatModuleCategoryPreadditiveHasZeroMorphismsInstPreadditiveModuleCatModuleCategory.{u1, u2} R _inst_1) M N)) (ModuleCat.of.{u1, u2} R _inst_1 (Prod.{u1, u1} (ModuleCat.carrier.{u1, u2} R _inst_1 M) (ModuleCat.carrier.{u1, u2} R _inst_1 N)) (Prod.instAddCommGroupSum.{u1, u1} (ModuleCat.carrier.{u1, u2} R _inst_1 M) (ModuleCat.carrier.{u1, u2} R _inst_1 N) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 M) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 N)) (Prod.module.{u2, u1, u1} R (ModuleCat.carrier.{u1, u2} R _inst_1 M) (ModuleCat.carrier.{u1, u2} R _inst_1 N) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u2} R _inst_1 M) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 M)) (AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u2} R _inst_1 N) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 N)) (ModuleCat.isModule.{u1, u2} R _inst_1 M) (ModuleCat.isModule.{u1, u2} R _inst_1 N)))
Case conversion may be inaccurate. Consider using '#align Module.biprod_iso_prod ModuleCat.biprodIsoProdₓ'. -/
/-- We verify that the biproduct in `Module R` is isomorphic to
the cartesian product of the underlying types:
-/
@[simps hom_apply]
noncomputable def biprodIsoProd (M N : ModuleCat.{v} R) :
    (M ⊞ N : ModuleCat.{v} R) ≅ ModuleCat.of R (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).IsLimit
#align Module.biprod_iso_prod ModuleCat.biprodIsoProd

/- warning: Module.biprod_iso_prod_inv_comp_fst -> ModuleCat.biprodIsoProd_inv_comp_fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.biprod_iso_prod_inv_comp_fst ModuleCat.biprodIsoProd_inv_comp_fstₓ'. -/
@[simp, elementwise]
theorem biprodIsoProd_inv_comp_fst (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.fst = LinearMap.fst R M N :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)
#align Module.biprod_iso_prod_inv_comp_fst ModuleCat.biprodIsoProd_inv_comp_fst

/- warning: Module.biprod_iso_prod_inv_comp_snd -> ModuleCat.biprodIsoProd_inv_comp_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.biprod_iso_prod_inv_comp_snd ModuleCat.biprodIsoProd_inv_comp_sndₓ'. -/
@[simp, elementwise]
theorem biprodIsoProd_inv_comp_snd (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.snd = LinearMap.snd R M N :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)
#align Module.biprod_iso_prod_inv_comp_snd ModuleCat.biprodIsoProd_inv_comp_snd

namespace HasLimit

variable {J : Type w} (f : J → ModuleCat.{max w v} R)

#print ModuleCat.HasLimit.lift /-
/-- The map from an arbitrary cone over a indexed family of abelian groups
to the cartesian product of those groups.
-/
@[simps]
def lift (s : Fan f) : s.pt ⟶ ModuleCat.of R (∀ j, f j)
    where
  toFun x j := s.π.app ⟨j⟩ x
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp
#align Module.has_limit.lift ModuleCat.HasLimit.lift
-/

#print ModuleCat.HasLimit.productLimitCone /-
/-- Construct limit data for a product in `Module R`, using `Module.of R (Π j, F.obj j)`.
-/
@[simps]
def productLimitCone : Limits.LimitCone (Discrete.functor f)
    where
  Cone :=
    { pt := ModuleCat.of R (∀ j, f j)
      π := Discrete.natTrans fun j => (LinearMap.proj j.as : (∀ j, f j) →ₗ[R] f j.as) }
  IsLimit :=
    { lift := lift f
      fac := fun s j => by cases j; ext; simp
      uniq := fun s m w => by
        ext (x j)
        dsimp only [has_limit.lift]
        simp only [LinearMap.coe_mk]
        exact congr_arg (fun g : s.X ⟶ f j => (g : s.X → f j) x) (w ⟨j⟩) }
#align Module.has_limit.product_limit_cone ModuleCat.HasLimit.productLimitCone
-/

end HasLimit

open HasLimit

variable {J : Type} (f : J → ModuleCat.{v} R)

/- warning: Module.biproduct_iso_pi -> ModuleCat.biproductIsoPi is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {J : Type} [_inst_2 : Fintype.{0} J] (f : J -> (ModuleCat.{u1, u2} R _inst_1)), CategoryTheory.Iso.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Limits.biproduct.{0, u1, max u2 (succ u1)} J (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.CategoryTheory.preadditive.{u1, u2} R _inst_1)) f (ModuleCat.biproductIsoPi._proof_1.{u2, u1} R _inst_1 J _inst_2 f)) (ModuleCat.of.{u1, u2} R _inst_1 (forall (j : J), coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) (f j)) (fun (i : J) => ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 (f i))) (Pi.module.{0, u1, u2} J (fun (j : J) => coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) (f j)) R (Ring.toSemiring.{u2} R _inst_1) (fun (i : J) => AddCommGroup.toAddCommMonoid.{u1} (coeSort.{max (succ u2) (succ (succ u1)), succ (succ u1)} (ModuleCat.{u1, u2} R _inst_1) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u2} R _inst_1) (f i)) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 (f i))) (fun (i : J) => ModuleCat.isModule.{u1, u2} R _inst_1 (f i))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {J : Type} [_inst_2 : Fintype.{0} J] (f : J -> (ModuleCat.{u1, u2} R _inst_1)), CategoryTheory.Iso.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Limits.biproduct.{0, u1, max u2 (succ u1)} J (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.instPreadditiveModuleCatModuleCategory.{u1, u2} R _inst_1)) f (CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct.{0, u1, max u2 (succ u1)} J (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.instPreadditiveModuleCatModuleCategory.{u1, u2} R _inst_1)) (CategoryTheory.Limits.hasBiproductsOfShape_finite.{0, u1, max u2 (succ u1)} J (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, max u2 (succ u1)} (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.instPreadditiveModuleCatModuleCategory.{u1, u2} R _inst_1)) (ModuleCat.instHasFiniteBiproductsModuleCatModuleCategoryPreadditiveHasZeroMorphismsInstPreadditiveModuleCatModuleCategory.{u1, u2} R _inst_1) (Finite.of_fintype.{0} J _inst_2)) f)) (ModuleCat.of.{u1, u2} R _inst_1 (forall (j : J), ModuleCat.carrier.{u1, u2} R _inst_1 (f j)) (Pi.addCommGroup.{0, u1} J (fun (j : J) => ModuleCat.carrier.{u1, u2} R _inst_1 (f j)) (fun (i : J) => ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 (f i))) (Pi.module.{0, u1, u2} J (fun (j : J) => ModuleCat.carrier.{u1, u2} R _inst_1 (f j)) R (Ring.toSemiring.{u2} R _inst_1) (fun (i : J) => AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u2} R _inst_1 (f i)) (ModuleCat.isAddCommGroup.{u1, u2} R _inst_1 (f i))) (fun (i : J) => ModuleCat.isModule.{u1, u2} R _inst_1 (f i))))
Case conversion may be inaccurate. Consider using '#align Module.biproduct_iso_pi ModuleCat.biproductIsoPiₓ'. -/
/-- We verify that the biproduct we've just defined is isomorphic to the `Module R` structure
on the dependent function type
-/
@[simps hom_apply]
noncomputable def biproductIsoPi [Fintype J] (f : J → ModuleCat.{v} R) :
    (⨁ f : ModuleCat.{v} R) ≅ ModuleCat.of R (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).IsLimit
#align Module.biproduct_iso_pi ModuleCat.biproductIsoPi

/- warning: Module.biproduct_iso_pi_inv_comp_π -> ModuleCat.biproductIsoPi_inv_comp_π is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.biproduct_iso_pi_inv_comp_π ModuleCat.biproductIsoPi_inv_comp_πₓ'. -/
@[simp, elementwise]
theorem biproductIsoPi_inv_comp_π [Fintype J] (f : J → ModuleCat.{v} R) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = (LinearMap.proj j : (∀ j, f j) →ₗ[R] f j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)
#align Module.biproduct_iso_pi_inv_comp_π ModuleCat.biproductIsoPi_inv_comp_π

end ModuleCat

section SplitExact

variable {R : Type u} {A M B : Type v} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup M] [Module R M]

variable {j : A →ₗ[R] M} {g : M →ₗ[R] B}

open ModuleCat

/- warning: lequiv_prod_of_right_split_exact -> lequivProdOfRightSplitExact is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lequiv_prod_of_right_split_exact lequivProdOfRightSplitExactₓ'. -/
/-- The isomorphism `A × B ≃ₗ[R] M` coming from a right split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequivProdOfRightSplitExact {f : B →ₗ[R] M} (hj : Function.Injective j)
    (exac : j.range = g.ker) (h : g.comp f = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  (({             RightSplit := ⟨asHom f, h⟩
                  mono := (ModuleCat.mono_iff_injective <| asHom j).mpr hj
                  exact := (exact_iff _ _).mpr exac } : RightSplit _ _).Splitting.Iso.trans <|
        biprodIsoProd _ _).toLinearEquiv.symm
#align lequiv_prod_of_right_split_exact lequivProdOfRightSplitExact

/- warning: lequiv_prod_of_left_split_exact -> lequivProdOfLeftSplitExact is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lequiv_prod_of_left_split_exact lequivProdOfLeftSplitExactₓ'. -/
/-- The isomorphism `A × B ≃ₗ[R] M` coming from a left split exact sequence `0 ⟶ A ⟶ M ⟶ B ⟶ 0`
of modules.-/
noncomputable def lequivProdOfLeftSplitExact {f : M →ₗ[R] A} (hg : Function.Surjective g)
    (exac : j.range = g.ker) (h : f.comp j = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  (({             LeftSplit := ⟨asHom f, h⟩
                  Epi := (ModuleCat.epi_iff_surjective <| asHom g).mpr hg
                  exact := (exact_iff _ _).mpr exac } : LeftSplit _ _).Splitting.Iso.trans <|
        biprodIsoProd _ _).toLinearEquiv.symm
#align lequiv_prod_of_left_split_exact lequivProdOfLeftSplitExact

end SplitExact

