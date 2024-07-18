/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import CategoryTheory.Preadditive.Basic
import Algebra.Module.LinearMap.Defs
import Algebra.Group.Invertible.Defs
import Algebra.Algebra.Defs

#align_import category_theory.linear.basic from "leanprover-community/mathlib"@"3dec44d0b621a174c56e994da4aae15ba60110a2"

/-!
# Linear categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An `R`-linear category is a category in which `X ⟶ Y` is an `R`-module in such a way that
composition of morphisms is `R`-linear in both variables.

Note that sometimes in the literature a "linear category" is further required to be abelian.

## Implementation

Corresponding to the fact that we need to have an `add_comm_group X` structure in place
to talk about a `module R X` structure,
we need `preadditive C` as a prerequisite typeclass for `linear R C`.
This makes for longer signatures than would be ideal.

## Future work

It would be nice to have a usable framework of enriched categories in which this just became
a category enriched in `Module R`.

-/


universe w v u

open CategoryTheory.Limits

open LinearMap

namespace CategoryTheory

#print CategoryTheory.Linear /-
/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
    `R`-linear in both variables. -/
class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  smul_comp' : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    obviously
  comp_smul' : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    obviously
#align category_theory.linear CategoryTheory.Linear
-/

attribute [instance] linear.hom_module

attribute [simp, reassoc] linear.smul_comp

attribute [reassoc, simp] linear.comp_smul

-- (the linter doesn't like `simp` on the `_assoc` lemma)
end CategoryTheory

open CategoryTheory

namespace CategoryTheory.Linear

variable {C : Type u} [Category.{v} C] [Preadditive C]

#print CategoryTheory.Linear.preadditiveNatLinear /-
instance preadditiveNatLinear : Linear ℕ C
    where
  smul_comp' X Y Z r f g := (Preadditive.rightComp X g).map_nsmul f r
  comp_smul' X Y Z f r g := (Preadditive.leftComp Z f).map_nsmul g r
#align category_theory.linear.preadditive_nat_linear CategoryTheory.Linear.preadditiveNatLinear
-/

#print CategoryTheory.Linear.preadditiveIntLinear /-
instance preadditiveIntLinear : Linear ℤ C
    where
  smul_comp' X Y Z r f g := (Preadditive.rightComp X g).map_zsmul f r
  comp_smul' X Y Z f r g := (Preadditive.leftComp Z f).map_zsmul g r
#align category_theory.linear.preadditive_int_linear CategoryTheory.Linear.preadditiveIntLinear
-/

section End

variable {R : Type w}

instance [Semiring R] [Linear R C] (X : C) : Module R (End X) := by dsimp [End]; infer_instance

instance [CommSemiring R] [Linear R C] (X : C) : Algebra R (End X) :=
  Algebra.ofModule (fun r f g => comp_smul _ _ _ _ _ _) fun r f g => smul_comp _ _ _ _ _ _

end End

section

variable {R : Type w} [Semiring R] [Linear R C]

section InducedCategory

universe u'

variable {C} {D : Type u'} (F : D → C)

#print CategoryTheory.Linear.inducedCategory /-
instance inducedCategory : Linear.{w, v} R (InducedCategory C F)
    where
  homModule X Y := @Linear.homModule R _ C _ _ _ (F X) (F Y)
  smul_comp' P Q R f f' g := smul_comp' _ _ _ _ _ _
  comp_smul' P Q R f g g' := comp_smul' _ _ _ _ _ _
#align category_theory.linear.induced_category CategoryTheory.Linear.inducedCategory
-/

end InducedCategory

#print CategoryTheory.Linear.fullSubcategory /-
instance fullSubcategory (Z : C → Prop) : Linear.{w, v} R (FullSubcategory Z)
    where
  homModule X Y := @Linear.homModule R _ C _ _ _ X.obj Y.obj
  smul_comp' P Q R f f' g := smul_comp' _ _ _ _ _ _
  comp_smul' P Q R f g g' := comp_smul' _ _ _ _ _ _
#align category_theory.linear.full_subcategory CategoryTheory.Linear.fullSubcategory
-/

variable (R)

#print CategoryTheory.Linear.leftComp /-
/-- Composition by a fixed left argument as an `R`-linear map. -/
@[simps]
def leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →ₗ[R] X ⟶ Z
    where
  toFun g := f ≫ g
  map_add' := by simp
  map_smul' := by simp
#align category_theory.linear.left_comp CategoryTheory.Linear.leftComp
-/

#print CategoryTheory.Linear.rightComp /-
/-- Composition by a fixed right argument as an `R`-linear map. -/
@[simps]
def rightComp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →ₗ[R] X ⟶ Z
    where
  toFun f := f ≫ g
  map_add' := by simp
  map_smul' := by simp
#align category_theory.linear.right_comp CategoryTheory.Linear.rightComp
-/

instance {X Y : C} (f : X ⟶ Y) [Epi f] (r : R) [Invertible r] : Epi (r • f) :=
  ⟨fun R g g' H =>
    by
    rw [smul_comp, smul_comp, ← comp_smul, ← comp_smul, cancel_epi] at H
    simpa [smul_smul] using congr_arg (fun f => ⅟ r • f) H⟩

instance {X Y : C} (f : X ⟶ Y) [Mono f] (r : R) [Invertible r] : Mono (r • f) :=
  ⟨fun R g g' H =>
    by
    rw [comp_smul, comp_smul, ← smul_comp, ← smul_comp, cancel_mono] at H
    simpa [smul_smul] using congr_arg (fun f => ⅟ r • f) H⟩

#print CategoryTheory.Linear.homCongr /-
/-- Given isomorphic objects `X ≅ Y, W ≅ Z` in a `k`-linear category, we have a `k`-linear
isomorphism between `Hom(X, W)` and `Hom(Y, Z).` -/
def homCongr (k : Type _) {C : Type _} [Category C] [Semiring k] [Preadditive C] [Linear k C]
    {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) : (X ⟶ W) ≃ₗ[k] Y ⟶ Z :=
  {
    (rightComp k Y f₂.hom).comp
      (leftComp k W
        f₁.symm.hom) with
    invFun := (leftComp k W f₁.hom).comp (rightComp k Y f₂.symm.hom)
    left_inv := fun x => by
      simp only [iso.symm_hom, LinearMap.toFun_eq_coe, LinearMap.coe_comp, Function.comp_apply,
        left_comp_apply, right_comp_apply, category.assoc, iso.hom_inv_id, category.comp_id,
        iso.hom_inv_id_assoc]
    right_inv := fun x => by
      simp only [iso.symm_hom, LinearMap.coe_comp, Function.comp_apply, right_comp_apply,
        left_comp_apply, LinearMap.toFun_eq_coe, iso.inv_hom_id_assoc, category.assoc,
        iso.inv_hom_id, category.comp_id] }
#align category_theory.linear.hom_congr CategoryTheory.Linear.homCongr
-/

#print CategoryTheory.Linear.homCongr_apply /-
theorem homCongr_apply (k : Type _) {C : Type _} [Category C] [Semiring k] [Preadditive C]
    [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : X ⟶ W) :
    homCongr k f₁ f₂ f = (f₁.inv ≫ f) ≫ f₂.hom :=
  rfl
#align category_theory.linear.hom_congr_apply CategoryTheory.Linear.homCongr_apply
-/

#print CategoryTheory.Linear.homCongr_symm_apply /-
theorem homCongr_symm_apply (k : Type _) {C : Type _} [Category C] [Semiring k] [Preadditive C]
    [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : Y ⟶ Z) :
    (homCongr k f₁ f₂).symm f = f₁.hom ≫ f ≫ f₂.inv :=
  rfl
#align category_theory.linear.hom_congr_symm_apply CategoryTheory.Linear.homCongr_symm_apply
-/

end

section

variable {S : Type w} [CommSemiring S] [Linear S C]

#print CategoryTheory.Linear.comp /-
/-- Composition as a bilinear map. -/
@[simps]
def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] (Y ⟶ Z) →ₗ[S] X ⟶ Z
    where
  toFun f := leftComp S Z f
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
#align category_theory.linear.comp CategoryTheory.Linear.comp
-/

end

end CategoryTheory.Linear

