/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.constructions.limits_of_products_and_equalizers
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Prod
import Mathbin.Data.Fintype.Sigma
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Preserves.Finite
import Mathbin.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathbin.CategoryTheory.Limits.Constructions.Equalizers
import Mathbin.CategoryTheory.Limits.Constructions.BinaryProducts

/-!
# Constructing limits from products and equalizers.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

If a functor preserves all products and equalizers, then it preserves all limits.
Similarly, if it preserves all finite products and equalizers, then it preserves all finite limits.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/


open CategoryTheory

open Opposite

namespace CategoryTheory.Limits

universe w v v₂ u u₂

variable {C : Type u} [Category.{v} C]

variable {J : Type w} [SmallCategory J]

-- We hide the "implementation details" inside a namespace
namespace HasLimitOfHasProductsOfHasEqualizers

variable {F : J ⥤ C} {c₁ : Fan F.obj} {c₂ : Fan fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.2}
  (s t : c₁.pt ⟶ c₂.pt)
  (hs : ∀ f : Σp : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
  (ht : ∀ f : Σp : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩) (i : Fork s t)

include hs ht

/- warning: category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_limit -> CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_limit CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimitₓ'. -/
/--
(Implementation) Given the appropriate product and equalizer cones, build the cone for `F` which is
limiting if the given cones are also.
-/
@[simps]
def buildLimit : Cone F where
  pt := i.pt
  π :=
    { app := fun j => i.ι ≫ c₁.π.app ⟨_⟩
      naturality' := fun j₁ j₂ f => by
        dsimp
        rw [category.id_comp, category.assoc, ← hs ⟨⟨_, _⟩, f⟩, i.condition_assoc, ht] }
#align category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_limit CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimit

variable {i}

/- warning: category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_is_limit -> CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildIsLimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_is_limit CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildIsLimitₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
/--
(Implementation) Show the cone constructed in `build_limit` is limiting, provided the cones used in
its construction are.
-/
def buildIsLimit (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) :
    IsLimit (buildLimit s t hs ht i)
    where
  lift q := by
    refine' hi.lift (fork.of_ι _ _)
    · refine' t₁.lift (fan.mk _ fun j => _)
      apply q.π.app j
    · apply t₂.hom_ext
      intro j
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]"
      simp [hs, ht]
  uniq q m w :=
    hi.hom_ext
      (i.equalizer_ext
        (t₁.hom_ext fun j => by
          cases j
          simpa using w j))
#align category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_is_limit CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildIsLimit

end HasLimitOfHasProductsOfHasEqualizers

open HasLimitOfHasProductsOfHasEqualizers

/- warning: category_theory.limits.limit_cone_of_equalizer_and_product -> CategoryTheory.Limits.limitConeOfEqualizerAndProduct is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F))] [_inst_4 : CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) (CategoryTheory.discreteCategory.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) (fun (f : Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) => CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F (Prod.snd.{u1, u1} J J (Sigma.fst.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)) f))))] [_inst_5 : CategoryTheory.Limits.HasEqualizers.{u2, u3} C _inst_1], CategoryTheory.Limits.LimitCone.{u1, u1, u2, u3} J _inst_2 C _inst_1 F
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F)))] [_inst_4 : CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) (CategoryTheory.discreteCategory.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) (fun (f : Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) (Prod.snd.{u1, u1} J J (Sigma.fst.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)) f))))] [_inst_5 : CategoryTheory.Limits.HasEqualizers.{u2, u3} C _inst_1], CategoryTheory.Limits.LimitCone.{u1, u1, u2, u3} J _inst_2 C _inst_1 F
Case conversion may be inaccurate. Consider using '#align category_theory.limits.limit_cone_of_equalizer_and_product CategoryTheory.Limits.limitConeOfEqualizerAndProductₓ'. -/
/-- Given the existence of the appropriate (possibly finite) products and equalizers,
we can construct a limit cone for `F`.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
noncomputable def limitConeOfEqualizerAndProduct (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    LimitCone F where
  Cone := _
  IsLimit :=
    buildIsLimit (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨_⟩ ≫ F.map f.2)
      (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨f.1.2⟩) (by simp) (by simp)
      (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)
#align category_theory.limits.limit_cone_of_equalizer_and_product CategoryTheory.Limits.limitConeOfEqualizerAndProduct

/- warning: category_theory.limits.has_limit_of_equalizer_and_product -> CategoryTheory.Limits.hasLimit_of_equalizer_and_product is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F))] [_inst_4 : CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) (CategoryTheory.discreteCategory.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) (fun (f : Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) => CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F (Prod.snd.{u1, u1} J J (Sigma.fst.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)) f))))] [_inst_5 : CategoryTheory.Limits.HasEqualizers.{u2, u3} C _inst_1], CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) [_inst_3 : CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F)))] [_inst_4 : CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) (CategoryTheory.discreteCategory.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) (fun (f : Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) (Prod.snd.{u1, u1} J J (Sigma.fst.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)) f))))] [_inst_5 : CategoryTheory.Limits.HasEqualizers.{u2, u3} C _inst_1], CategoryTheory.Limits.HasLimit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_limit_of_equalizer_and_product CategoryTheory.Limits.hasLimit_of_equalizer_and_productₓ'. -/
/--
Given the existence of the appropriate (possibly finite) products and equalizers, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
theorem hasLimit_of_equalizer_and_product (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    HasLimit F :=
  HasLimit.mk (limitConeOfEqualizerAndProduct F)
#align category_theory.limits.has_limit_of_equalizer_and_product CategoryTheory.Limits.hasLimit_of_equalizer_and_product

/- warning: category_theory.limits.limit_subobject_product -> CategoryTheory.Limits.limitSubobjectProduct is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_3 : CategoryTheory.Limits.HasLimitsOfSize.{u1, u1, u2, u3} C _inst_1] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1), Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Limits.limit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F (CategoryTheory.Limits.limitSubobjectProduct._proof_1.{u3, u2, u1} C _inst_1 J _inst_2 _inst_3 F)) (CategoryTheory.Limits.piObj.{u1, u2, u3} J C _inst_1 (fun (j : J) => CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F j) (CategoryTheory.Limits.limitSubobjectProduct._proof_2.{u3, u2, u1} C _inst_1 J _inst_2 _inst_3 F))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_3 : CategoryTheory.Limits.HasLimitsOfSize.{u1, u1, u2, u3} C _inst_1] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1), Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Limits.limit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{u1, u1, u2, u3} C _inst_1 J _inst_2 (CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u2, u3} C _inst_1 J _inst_2 _inst_3) F)) (CategoryTheory.Limits.piObj.{u1, u2, u3} J C _inst_1 (fun (j : J) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) j) (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{u1, u1, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) _inst_3) (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (fun (j : J) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) j))))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.limit_subobject_product CategoryTheory.Limits.limitSubobjectProductₓ'. -/
/-- A limit can be realised as a subobject of a product. -/
noncomputable def limitSubobjectProduct [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    limit F ⟶ ∏ fun j => F.obj j :=
  (limit.isoLimitCone (limitConeOfEqualizerAndProduct F)).hom ≫ equalizer.ι _ _
#align category_theory.limits.limit_subobject_product CategoryTheory.Limits.limitSubobjectProduct

/- warning: category_theory.limits.limit_subobject_product_mono -> CategoryTheory.Limits.limitSubobjectProduct_mono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_3 : CategoryTheory.Limits.HasLimitsOfSize.{u1, u1, u2, u3} C _inst_1] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1), CategoryTheory.Mono.{u2, u3} C _inst_1 (CategoryTheory.Limits.limit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F (CategoryTheory.Limits.limitSubobjectProduct._proof_1.{u3, u2, u1} C _inst_1 J _inst_2 _inst_3 F)) (CategoryTheory.Limits.piObj.{u1, u2, u3} J C _inst_1 (fun (j : J) => CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F j) (CategoryTheory.Limits.limitSubobjectProduct._proof_2.{u3, u2, u1} C _inst_1 J _inst_2 _inst_3 F)) (CategoryTheory.Limits.limitSubobjectProduct.{u1, u2, u3} C _inst_1 J _inst_2 _inst_3 F)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_3 : CategoryTheory.Limits.HasLimitsOfSize.{u1, u1, u2, u3} C _inst_1] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1), CategoryTheory.Mono.{u2, u3} C _inst_1 (CategoryTheory.Limits.limit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{u1, u1, u2, u3} C _inst_1 J _inst_2 (CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u2, u3} C _inst_1 J _inst_2 _inst_3) F)) (CategoryTheory.Limits.piObj.{u1, u2, u3} J C _inst_1 (fun (j : J) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) j) (CategoryTheory.Limits.hasLimitOfHasLimitsOfShape.{u1, u1, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits.{u1, u1, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) _inst_3) (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (fun (j : J) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) j)))) (CategoryTheory.Limits.limitSubobjectProduct.{u1, u2, u3} C _inst_1 J _inst_2 _inst_3 F)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.limit_subobject_product_mono CategoryTheory.Limits.limitSubobjectProduct_monoₓ'. -/
instance limitSubobjectProduct_mono [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Mono (limitSubobjectProduct F) :=
  mono_comp _ _
#align category_theory.limits.limit_subobject_product_mono CategoryTheory.Limits.limitSubobjectProduct_mono

#print CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products /-
/-- Any category with products and equalizers has all limits.

See <https://stacks.math.columbia.edu/tag/002N>.
-/
theorem has_limits_of_hasEqualizers_and_products [HasProducts.{w} C] [HasEqualizers C] :
    HasLimitsOfSize.{w, w} C :=
  { HasLimitsOfShape := fun J 𝒥 => { HasLimit := fun F => has_limit_of_equalizer_and_product F } }
#align category_theory.limits.has_limits_of_has_equalizers_and_products CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products
-/

#print CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products /-
/-- Any category with finite products and equalizers has all finite limits.

See <https://stacks.math.columbia.edu/tag/002O>.
-/
theorem hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C]
    [HasEqualizers C] : HasFiniteLimits C :=
  ⟨fun J _ _ => { HasLimit := fun F => has_limit_of_equalizer_and_product F }⟩
#align category_theory.limits.has_finite_limits_of_has_equalizers_and_finite_products CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products
-/

variable {D : Type u₂} [Category.{v₂} D]

noncomputable section

section

variable [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Discrete (Σp : J × J, p.1 ⟶ p.2)) C]
  [HasEqualizers C]

variable (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
  [PreservesLimitsOfShape (Discrete.{w} J) G]
  [PreservesLimitsOfShape (Discrete.{w} (Σp : J × J, p.1 ⟶ p.2)) G]

#print CategoryTheory.Limits.preservesLimitOfPreservesEqualizersAndProduct /-
/-- If a functor preserves equalizers and the appropriate products, it preserves limits. -/
def preservesLimitOfPreservesEqualizersAndProduct : PreservesLimitsOfShape J G
    where PreservesLimit K := by
    let P := ∏ K.obj
    let Q := ∏ fun f : Σp : J × J, p.fst ⟶ p.snd => K.obj f.1.2
    let s : P ⟶ Q := pi.lift fun f => limit.π (discrete.functor K.obj) ⟨_⟩ ≫ K.map f.2
    let t : P ⟶ Q := pi.lift fun f => limit.π (discrete.functor K.obj) ⟨f.1.2⟩
    let I := equalizer s t
    let i : I ⟶ P := equalizer.ι s t
    apply
      preserves_limit_of_preserves_limit_cone
        (build_is_limit s t (by simp) (by simp) (limit.is_limit _) (limit.is_limit _)
          (limit.is_limit _))
    refine' is_limit.of_iso_limit (build_is_limit _ _ _ _ _ _ _) _
    · exact fan.mk _ fun j => G.map (pi.π _ j)
    · exact fan.mk (G.obj Q) fun f => G.map (pi.π _ f)
    · apply G.map s
    · apply G.map t
    · intro f
      dsimp
      simp only [← G.map_comp, limit.lift_π, fan.mk_π_app]
    · intro f
      dsimp
      simp only [← G.map_comp, limit.lift_π, fan.mk_π_app]
    · apply fork.of_ι (G.map i) _
      simp only [← G.map_comp, equalizer.condition]
    · apply is_limit_of_has_product_of_preserves_limit
    · apply is_limit_of_has_product_of_preserves_limit
    · apply is_limit_fork_map_of_is_limit
      apply equalizer_is_equalizer
    refine' cones.ext (iso.refl _) _
    intro j
    dsimp
    simp
#align category_theory.limits.preserves_limit_of_preserves_equalizers_and_product CategoryTheory.Limits.preservesLimitOfPreservesEqualizersAndProduct
-/

-- See note [dsimp, simp].
end

/- warning: category_theory.limits.preserves_finite_limits_of_preserves_equalizers_and_finite_products -> CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasEqualizers.{u1, u3} C _inst_1] [_inst_5 : CategoryTheory.Limits.HasFiniteProducts.{u1, u3} C _inst_1] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_6 : CategoryTheory.Limits.PreservesLimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory G] [_inst_7 : forall (J : Type) [_inst_8 : Fintype.{0} J], CategoryTheory.Limits.PreservesLimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 (CategoryTheory.Discrete.{0} J) (CategoryTheory.discreteCategory.{0} J) G], CategoryTheory.Limits.PreservesFiniteLimits.{u1, u2, u3, u4} C _inst_1 D _inst_3 G
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasEqualizers.{u1, u3} C _inst_1] [_inst_5 : CategoryTheory.Limits.HasFiniteProducts.{u1, u3} C _inst_1] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_6 : CategoryTheory.Limits.PreservesLimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory G] [_inst_7 : CategoryTheory.Limits.PreservesFiniteProducts.{u1, u2, u3, u4} C _inst_1 D _inst_3 G], CategoryTheory.Limits.PreservesFiniteLimits.{u1, u2, u3, u4} C _inst_1 D _inst_3 G
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_finite_limits_of_preserves_equalizers_and_finite_products CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProductsₓ'. -/
/-- If G preserves equalizers and finite products, it preserves finite limits. -/
def preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts [HasEqualizers C]
    [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [∀ (J : Type) [Fintype J], PreservesLimitsOfShape (Discrete J) G] : PreservesFiniteLimits G :=
  ⟨fun _ _ _ => preserves_limit_of_preserves_equalizers_and_product G⟩
#align category_theory.limits.preserves_finite_limits_of_preserves_equalizers_and_finite_products CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts

#print CategoryTheory.Limits.preservesLimitsOfPreservesEqualizersAndProducts /-
/-- If G preserves equalizers and products, it preserves all limits. -/
def preservesLimitsOfPreservesEqualizersAndProducts [HasEqualizers C] [HasProducts.{w} C]
    (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [∀ J, PreservesLimitsOfShape (Discrete.{w} J) G] : PreservesLimitsOfSize.{w, w} G
    where PreservesLimitsOfShape J 𝒥 := preserves_limit_of_preserves_equalizers_and_product G
#align category_theory.limits.preserves_limits_of_preserves_equalizers_and_products CategoryTheory.Limits.preservesLimitsOfPreservesEqualizersAndProducts
-/

#print CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks /-
theorem hasFiniteLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasFiniteLimits C :=
  @hasFiniteLimits_of_hasEqualizers_and_finite_products _
    (@hasFiniteProducts_of_has_binary_and_terminal _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
    (@hasEqualizers_of_hasPullbacks_and_binary_products _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
#align category_theory.limits.has_finite_limits_of_has_terminal_and_pullbacks CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks
-/

#print CategoryTheory.Limits.preservesFiniteLimitsOfPreservesTerminalAndPullbacks /-
/-- If G preserves terminal objects and pullbacks, it preserves all finite limits. -/
def preservesFiniteLimitsOfPreservesTerminalAndPullbacks [HasTerminal C] [HasPullbacks C]
    (G : C ⥤ D) [PreservesLimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesLimitsOfShape WalkingCospan G] : PreservesFiniteLimits G :=
  by
  haveI : has_finite_limits C := has_finite_limits_of_has_terminal_and_pullbacks
  haveI : preserves_limits_of_shape (discrete walking_pair) G :=
    preservesBinaryProductsOfPreservesTerminalAndPullbacks G
  exact
    @preserves_finite_limits_of_preserves_equalizers_and_finite_products _ _ _ _ G
      (preserves_equalizers_of_preserves_pullbacks_and_binary_products G)
      (preserves_finite_products_of_preserves_binary_and_terminal G)
#align category_theory.limits.preserves_finite_limits_of_preserves_terminal_and_pullbacks CategoryTheory.Limits.preservesFiniteLimitsOfPreservesTerminalAndPullbacks
-/

/-!
We now dualize the above constructions, resorting to copy-paste.
-/


-- We hide the "implementation details" inside a namespace
namespace HasColimitOfHasCoproductsOfHasCoequalizers

variable {F : J ⥤ C} {c₁ : Cofan fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.1} {c₂ : Cofan F.obj}
  (s t : c₁.pt ⟶ c₂.pt)
  (hs : ∀ f : Σp : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
  (ht : ∀ f : Σp : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩) (i : Cofork s t)

include hs ht

/- warning: category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_colimit -> CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_colimit CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildColimitₓ'. -/
/-- (Implementation) Given the appropriate coproduct and coequalizer cocones,
build the cocone for `F` which is colimiting if the given cocones are also.
-/
@[simps]
def buildColimit : Cocone F where
  pt := i.pt
  ι :=
    { app := fun j => c₂.ι.app ⟨_⟩ ≫ i.π
      naturality' := fun j₁ j₂ f => by
        dsimp
        rw [category.comp_id, ← reassoc_of (hs ⟨⟨_, _⟩, f⟩), i.condition, ← category.assoc, ht] }
#align category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_colimit CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit

variable {i}

/- warning: category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_is_colimit -> CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_is_colimit CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimitₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
/-- (Implementation) Show the cocone constructed in `build_colimit` is colimiting,
provided the cocones used in its construction are.
-/
def buildIsColimit (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) :
    IsColimit (buildColimit s t hs ht i)
    where
  desc q := by
    refine' hi.desc (cofork.of_π _ _)
    · refine' t₂.desc (cofan.mk _ fun j => _)
      apply q.ι.app j
    · apply t₁.hom_ext
      intro j
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]"
      simp [reassoc_of hs, reassoc_of ht]
  uniq q m w :=
    hi.hom_ext
      (i.coequalizer_ext
        (t₂.hom_ext fun j => by
          cases j
          simpa using w j))
#align category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_is_colimit CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit

end HasColimitOfHasCoproductsOfHasCoequalizers

open HasColimitOfHasCoproductsOfHasCoequalizers

/- warning: category_theory.limits.colimit_cocone_of_coequalizer_and_coproduct -> CategoryTheory.Limits.colimitCoconeOfCoequalizerAndCoproduct is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) [_inst_4 : CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F))] [_inst_5 : CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) (CategoryTheory.discreteCategory.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) (fun (f : Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) => CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F (Prod.fst.{u1, u1} J J (Sigma.fst.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)) f))))] [_inst_6 : CategoryTheory.Limits.HasCoequalizers.{u2, u3} C _inst_1], CategoryTheory.Limits.ColimitCocone.{u1, u1, u2, u3} J _inst_2 C _inst_1 F
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) [_inst_4 : CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F)))] [_inst_5 : CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) (CategoryTheory.discreteCategory.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) (fun (f : Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) (Prod.fst.{u1, u1} J J (Sigma.fst.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)) f))))] [_inst_6 : CategoryTheory.Limits.HasCoequalizers.{u2, u3} C _inst_1], CategoryTheory.Limits.ColimitCocone.{u1, u1, u2, u3} J _inst_2 C _inst_1 F
Case conversion may be inaccurate. Consider using '#align category_theory.limits.colimit_cocone_of_coequalizer_and_coproduct CategoryTheory.Limits.colimitCoconeOfCoequalizerAndCoproductₓ'. -/
/-- Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we can construct a colimit cocone for `F`.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
noncomputable def colimitCoconeOfCoequalizerAndCoproduct (F : J ⥤ C)
    [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : ColimitCocone F
    where
  Cocone := _
  IsColimit :=
    buildIsColimit (Sigma.desc fun f => F.map f.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨f.1.2⟩)
      (Sigma.desc fun f => colimit.ι (Discrete.functor F.obj) ⟨f.1.1⟩) (by simp) (by simp)
      (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
#align category_theory.limits.colimit_cocone_of_coequalizer_and_coproduct CategoryTheory.Limits.colimitCoconeOfCoequalizerAndCoproduct

/- warning: category_theory.limits.has_colimit_of_coequalizer_and_coproduct -> CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproduct is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) [_inst_4 : CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F))] [_inst_5 : CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) (CategoryTheory.discreteCategory.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) (fun (f : Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) => CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F (Prod.fst.{u1, u1} J J (Sigma.fst.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)) f))))] [_inst_6 : CategoryTheory.Limits.HasCoequalizers.{u2, u3} C _inst_1], CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1) [_inst_4 : CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F)))] [_inst_5 : CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} (CategoryTheory.Discrete.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) (CategoryTheory.discreteCategory.{u1} (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)))) C _inst_1 (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 (Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) (fun (f : Sigma.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p))) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) (Prod.fst.{u1, u1} J J (Sigma.fst.{u1, u1} (Prod.{u1, u1} J J) (fun (p : Prod.{u1, u1} J J) => Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (Prod.fst.{u1, u1} J J p) (Prod.snd.{u1, u1} J J p)) f))))] [_inst_6 : CategoryTheory.Limits.HasCoequalizers.{u2, u3} C _inst_1], CategoryTheory.Limits.HasColimit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F
Case conversion may be inaccurate. Consider using '#align category_theory.limits.has_colimit_of_coequalizer_and_coproduct CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproductₓ'. -/
/-- Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we know a colimit of `F` exists.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
theorem hasColimit_of_coequalizer_and_coproduct (F : J ⥤ C) [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : HasColimit F :=
  HasColimit.mk (colimitCoconeOfCoequalizerAndCoproduct F)
#align category_theory.limits.has_colimit_of_coequalizer_and_coproduct CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproduct

/- warning: category_theory.limits.colimit_quotient_coproduct -> CategoryTheory.Limits.colimitQuotientCoproduct is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.Limits.HasColimitsOfSize.{u1, u1, u2, u3} C _inst_1] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1), Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Limits.sigmaObj.{u1, u2, u3} J C _inst_1 (fun (j : J) => CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F j) (CategoryTheory.Limits.colimitQuotientCoproduct._proof_1.{u3, u2, u1} C _inst_1 J _inst_2 _inst_4 F)) (CategoryTheory.Limits.colimit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F (CategoryTheory.Limits.colimitQuotientCoproduct._proof_2.{u3, u2, u1} C _inst_1 J _inst_2 _inst_4 F))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.Limits.HasColimitsOfSize.{u1, u1, u2, u3} C _inst_1] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1), Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Limits.sigmaObj.{u1, u2, u3} J C _inst_1 (fun (j : J) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) j) (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u1, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Limits.hasColimitsOfShapeOfHasColimitsOfSize.{u1, u1, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) _inst_4) (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (fun (j : J) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) j)))) (CategoryTheory.Limits.colimit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u1, u2, u3} C _inst_1 J _inst_2 (CategoryTheory.Limits.hasColimitsOfShapeOfHasColimitsOfSize.{u1, u1, u2, u3} C _inst_1 J _inst_2 _inst_4) F))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.colimit_quotient_coproduct CategoryTheory.Limits.colimitQuotientCoproductₓ'. -/
/-- A colimit can be realised as a quotient of a coproduct. -/
noncomputable def colimitQuotientCoproduct [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    (∐ fun j => F.obj j) ⟶ colimit F :=
  coequalizer.π _ _ ≫ (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)).inv
#align category_theory.limits.colimit_quotient_coproduct CategoryTheory.Limits.colimitQuotientCoproduct

/- warning: category_theory.limits.colimit_quotient_coproduct_epi -> CategoryTheory.Limits.colimitQuotientCoproduct_epi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.Limits.HasColimitsOfSize.{u1, u1, u2, u3} C _inst_1] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1), CategoryTheory.Epi.{u2, u3} C _inst_1 (CategoryTheory.Limits.sigmaObj.{u1, u2, u3} J C _inst_1 (fun (j : J) => CategoryTheory.Functor.obj.{u1, u2, u1, u3} J _inst_2 C _inst_1 F j) (CategoryTheory.Limits.colimitQuotientCoproduct._proof_1.{u3, u2, u1} C _inst_1 J _inst_2 _inst_4 F)) (CategoryTheory.Limits.colimit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F (CategoryTheory.Limits.colimitQuotientCoproduct._proof_2.{u3, u2, u1} C _inst_1 J _inst_2 _inst_4 F)) (CategoryTheory.Limits.colimitQuotientCoproduct.{u1, u2, u3} C _inst_1 J _inst_2 _inst_4 F)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.Limits.HasColimitsOfSize.{u1, u1, u2, u3} C _inst_1] (F : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_2 C _inst_1), CategoryTheory.Epi.{u2, u3} C _inst_1 (CategoryTheory.Limits.sigmaObj.{u1, u2, u3} J C _inst_1 (fun (j : J) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) j) (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u1, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Limits.hasColimitsOfShapeOfHasColimitsOfSize.{u1, u1, u2, u3} C _inst_1 (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) _inst_4) (CategoryTheory.Discrete.functor.{u2, u1, u3} C _inst_1 J (fun (j : J) => Prefunctor.obj.{succ u1, succ u2, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} J _inst_2 C _inst_1 F) j)))) (CategoryTheory.Limits.colimit.{u1, u1, u2, u3} J _inst_2 C _inst_1 F (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u1, u2, u3} C _inst_1 J _inst_2 (CategoryTheory.Limits.hasColimitsOfShapeOfHasColimitsOfSize.{u1, u1, u2, u3} C _inst_1 J _inst_2 _inst_4) F)) (CategoryTheory.Limits.colimitQuotientCoproduct.{u1, u2, u3} C _inst_1 J _inst_2 _inst_4 F)
Case conversion may be inaccurate. Consider using '#align category_theory.limits.colimit_quotient_coproduct_epi CategoryTheory.Limits.colimitQuotientCoproduct_epiₓ'. -/
instance colimitQuotientCoproduct_epi [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Epi (colimitQuotientCoproduct F) :=
  epi_comp _ _
#align category_theory.limits.colimit_quotient_coproduct_epi CategoryTheory.Limits.colimitQuotientCoproduct_epi

#print CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts /-
/-- Any category with coproducts and coequalizers has all colimits.

See <https://stacks.math.columbia.edu/tag/002P>.
-/
theorem has_colimits_of_hasCoequalizers_and_coproducts [HasCoproducts.{w} C] [HasCoequalizers C] :
    HasColimitsOfSize.{w, w} C :=
  {
    HasColimitsOfShape := fun J 𝒥 =>
      { HasColimit := fun F => has_colimit_of_coequalizer_and_coproduct F } }
#align category_theory.limits.has_colimits_of_has_coequalizers_and_coproducts CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts
-/

#print CategoryTheory.Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts /-
/-- Any category with finite coproducts and coequalizers has all finite colimits.

See <https://stacks.math.columbia.edu/tag/002Q>.
-/
theorem hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts [HasFiniteCoproducts C]
    [HasCoequalizers C] : HasFiniteColimits C :=
  ⟨fun J _ _ => { HasColimit := fun F => has_colimit_of_coequalizer_and_coproduct F }⟩
#align category_theory.limits.has_finite_colimits_of_has_coequalizers_and_finite_coproducts CategoryTheory.Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
-/

noncomputable section

section

variable [HasColimitsOfShape (Discrete.{w} J) C]
  [HasColimitsOfShape (Discrete.{w} (Σp : J × J, p.1 ⟶ p.2)) C] [HasCoequalizers C]

variable (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
  [PreservesColimitsOfShape (Discrete.{w} J) G]
  [PreservesColimitsOfShape (Discrete.{w} (Σp : J × J, p.1 ⟶ p.2)) G]

#print CategoryTheory.Limits.preservesColimitOfPreservesCoequalizersAndCoproduct /-
/-- If a functor preserves coequalizers and the appropriate coproducts, it preserves colimits. -/
def preservesColimitOfPreservesCoequalizersAndCoproduct : PreservesColimitsOfShape J G
    where PreservesColimit K := by
    let P := ∐ K.obj
    let Q := ∐ fun f : Σp : J × J, p.fst ⟶ p.snd => K.obj f.1.1
    let s : Q ⟶ P := sigma.desc fun f => K.map f.2 ≫ colimit.ι (discrete.functor K.obj) ⟨_⟩
    let t : Q ⟶ P := sigma.desc fun f => colimit.ι (discrete.functor K.obj) ⟨f.1.1⟩
    let I := coequalizer s t
    let i : P ⟶ I := coequalizer.π s t
    apply
      preserves_colimit_of_preserves_colimit_cocone
        (build_is_colimit s t (by simp) (by simp) (colimit.is_colimit _) (colimit.is_colimit _)
          (colimit.is_colimit _))
    refine' is_colimit.of_iso_colimit (build_is_colimit _ _ _ _ _ _ _) _
    · exact cofan.mk (G.obj Q) fun j => G.map (sigma.ι _ j)
    · exact cofan.mk _ fun f => G.map (sigma.ι _ f)
    · apply G.map s
    · apply G.map t
    · intro f
      dsimp
      simp only [← G.map_comp, colimit.ι_desc, cofan.mk_ι_app]
    · intro f
      dsimp
      simp only [← G.map_comp, colimit.ι_desc, cofan.mk_ι_app]
    · apply cofork.of_π (G.map i) _
      simp only [← G.map_comp, coequalizer.condition]
    · apply is_colimit_of_has_coproduct_of_preserves_colimit
    · apply is_colimit_of_has_coproduct_of_preserves_colimit
    · apply is_colimit_cofork_map_of_is_colimit
      apply coequalizer_is_coequalizer
    refine' cocones.ext (iso.refl _) _
    intro j
    dsimp
    simp
#align category_theory.limits.preserves_colimit_of_preserves_coequalizers_and_coproduct CategoryTheory.Limits.preservesColimitOfPreservesCoequalizersAndCoproduct
-/

-- See note [dsimp, simp].
end

/- warning: category_theory.limits.preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts -> CategoryTheory.Limits.preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproducts is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasCoequalizers.{u1, u3} C _inst_1] [_inst_5 : CategoryTheory.Limits.HasFiniteCoproducts.{u1, u3} C _inst_1] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_6 : CategoryTheory.Limits.PreservesColimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory G] [_inst_7 : forall (J : Type) [_inst_8 : Fintype.{0} J], CategoryTheory.Limits.PreservesColimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 (CategoryTheory.Discrete.{0} J) (CategoryTheory.discreteCategory.{0} J) G], CategoryTheory.Limits.PreservesFiniteColimits.{u1, u2, u3, u4} C _inst_1 D _inst_3 G
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.Limits.HasCoequalizers.{u1, u3} C _inst_1] [_inst_5 : CategoryTheory.Limits.HasFiniteCoproducts.{u1, u3} C _inst_1] (G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_3) [_inst_6 : CategoryTheory.Limits.PreservesColimitsOfShape.{0, 0, u1, u2, u3, u4} C _inst_1 D _inst_3 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory G] [_inst_7 : CategoryTheory.Limits.PreservesFiniteCoproducts.{u1, u2, u3, u4} C _inst_1 D _inst_3 G], CategoryTheory.Limits.PreservesFiniteColimits.{u1, u2, u3, u4} C _inst_1 D _inst_3 G
Case conversion may be inaccurate. Consider using '#align category_theory.limits.preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts CategoryTheory.Limits.preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproductsₓ'. -/
/-- If G preserves coequalizers and finite coproducts, it preserves finite colimits. -/
def preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproducts [HasCoequalizers C]
    [HasFiniteCoproducts C] (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
    [∀ (J) [Fintype J], PreservesColimitsOfShape (Discrete.{0} J) G] : PreservesFiniteColimits G :=
  ⟨fun _ _ _ => preserves_colimit_of_preserves_coequalizers_and_coproduct G⟩
#align category_theory.limits.preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts CategoryTheory.Limits.preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproducts

#print CategoryTheory.Limits.preservesColimitsOfPreservesCoequalizersAndCoproducts /-
/-- If G preserves coequalizers and coproducts, it preserves all colimits. -/
def preservesColimitsOfPreservesCoequalizersAndCoproducts [HasCoequalizers C] [HasCoproducts.{w} C]
    (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
    [∀ J, PreservesColimitsOfShape (Discrete.{w} J) G] : PreservesColimitsOfSize.{w} G
    where PreservesColimitsOfShape J 𝒥 :=
    preserves_colimit_of_preserves_coequalizers_and_coproduct G
#align category_theory.limits.preserves_colimits_of_preserves_coequalizers_and_coproducts CategoryTheory.Limits.preservesColimitsOfPreservesCoequalizersAndCoproducts
-/

#print CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts /-
theorem hasFiniteColimits_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasFiniteColimits C :=
  @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts _
    (@hasFiniteCoproducts_of_has_binary_and_initial _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
    (@hasCoequalizers_of_hasPushouts_and_binary_coproducts _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
#align category_theory.limits.has_finite_colimits_of_has_initial_and_pushouts CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts
-/

#print CategoryTheory.Limits.preservesFiniteColimitsOfPreservesInitialAndPushouts /-
/-- If G preserves initial objects and pushouts, it preserves all finite colimits. -/
def preservesFiniteColimitsOfPreservesInitialAndPushouts [HasInitial C] [HasPushouts C] (G : C ⥤ D)
    [PreservesColimitsOfShape (Discrete.{0} PEmpty) G] [PreservesColimitsOfShape WalkingSpan G] :
    PreservesFiniteColimits G :=
  by
  haveI : has_finite_colimits C := has_finite_colimits_of_has_initial_and_pushouts
  haveI : preserves_colimits_of_shape (discrete walking_pair) G :=
    preservesBinaryCoproductsOfPreservesInitialAndPushouts G
  exact
    @preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts _ _ _ _ G
      (preserves_coequalizers_of_preserves_pushouts_and_binary_coproducts G)
      (preserves_finite_coproducts_of_preserves_binary_and_initial G)
#align category_theory.limits.preserves_finite_colimits_of_preserves_initial_and_pushouts CategoryTheory.Limits.preservesFiniteColimitsOfPreservesInitialAndPushouts
-/

end CategoryTheory.Limits

