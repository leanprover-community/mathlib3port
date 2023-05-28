/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison

! This file was ported from Lean 3 source module category_theory.abelian.right_derived
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.InjectiveResolution
import Mathbin.Algebra.Homology.Additive
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono
import Mathbin.CategoryTheory.Abelian.Homology
import Mathbin.CategoryTheory.Abelian.Exact

/-!
# Right-derived functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the right-derived functors `F.right_derived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

The definition is
```
injective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
```
that is, we pick an injective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these right-derived functors can be calculated
on objects using any choice of injective resolution,
and on morphisms by any choice of lift to a cochain map between chosen injective resolutions.

Similarly we define natural transformations between right-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `category_theory.functor.right_derived_obj_injective_zero`: the `0`-th derived functor of `F` on
  an injective object `X` is isomorphic to `F.obj X`.
* `category_theory.functor.right_derived_obj_injective_succ`: injective objects have no higher
  right derived functor.
* `category_theory.nat_trans.right_derived`: the natural isomorphism between right derived functors
  induced by natural transformation.

Now, we assume `preserves_finite_limits F`, then
* `category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono`: if `f` is
  mono and `exact f g`, then `exact (F.map f) (F.map g)`.
* `category_theory.abelian.functor.right_derived_zero_iso_self`: if there are enough injectives,
  then there is a natural isomorphism `(F.right_derived 0) ≅ F`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {D : Type _} [Category D]

variable [Abelian C] [HasInjectiveResolutions C] [Abelian D]

#print CategoryTheory.Functor.rightDerived /-
/-- The right derived functors of an additive functor. -/
def Functor.rightDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor D _ n
#align category_theory.functor.right_derived CategoryTheory.Functor.rightDerived
-/

/- warning: category_theory.functor.right_derived_obj_iso -> CategoryTheory.Functor.rightDerivedObjIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.right_derived_obj_iso CategoryTheory.Functor.rightDerivedObjIsoₓ'. -/
/-- We can compute a right derived functor using a chosen injective resolution. -/
@[simps]
def Functor.rightDerivedObjIso (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C}
    (P : InjectiveResolution X) :
    (F.rightDerived n).obj X ≅
      (homologyFunctor D _ n).obj ((F.mapHomologicalComplex _).obj P.cocomplex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
      (HomotopyCategory.isoOfHomotopyEquiv
        (F.mapHomotopyEquiv (InjectiveResolution.homotopyEquiv _ P))) ≪≫
    (HomotopyCategory.homologyFactors D _ n).app _
#align category_theory.functor.right_derived_obj_iso CategoryTheory.Functor.rightDerivedObjIso

/- warning: category_theory.functor.right_derived_obj_injective_zero -> CategoryTheory.Functor.rightDerivedObjInjectiveZero is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.HasInjectiveResolutions.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Functor.rightDerivedObjInjectiveZero._proof_1.{u2, u1} C _inst_1 _inst_3)] [_inst_5 : CategoryTheory.Abelian.{u4, u3} D _inst_2] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) [_inst_6 : CategoryTheory.Functor.Additive.{u2, u3, u1, u4} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u4, u3} D _inst_2 _inst_5) F] (X : C) [_inst_7 : CategoryTheory.Injective.{u1, u2} C _inst_1 X], CategoryTheory.Iso.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) X) (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 F X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.HasInjectiveResolutions.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3))] [_inst_5 : CategoryTheory.Abelian.{u4, u3} D _inst_2] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) [_inst_6 : CategoryTheory.Functor.Additive.{u2, u3, u1, u4} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u4, u3} D _inst_2 _inst_5) F] (X : C) [_inst_7 : CategoryTheory.Injective.{u1, u2} C _inst_1 X], CategoryTheory.Iso.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) X) (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 F) X)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.right_derived_obj_injective_zero CategoryTheory.Functor.rightDerivedObjInjectiveZeroₓ'. -/
/-- The 0-th derived functor of `F` on an injective object `X` is just `F.obj X`. -/
@[simps]
def Functor.rightDerivedObjInjectiveZero (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    (F.rightDerived 0).obj X ≅ F.obj X :=
  F.rightDerivedObjIso 0 (InjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((CochainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (CochainComplex.homologyFunctor0Single₀ D).app (F.obj X)
#align category_theory.functor.right_derived_obj_injective_zero CategoryTheory.Functor.rightDerivedObjInjectiveZero

open ZeroObject

/- warning: category_theory.functor.right_derived_obj_injective_succ -> CategoryTheory.Functor.rightDerivedObjInjectiveSucc is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.HasInjectiveResolutions.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Functor.rightDerivedObjInjectiveSucc._proof_1.{u2, u1} C _inst_1 _inst_3)] [_inst_5 : CategoryTheory.Abelian.{u4, u3} D _inst_2] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) [_inst_6 : CategoryTheory.Functor.Additive.{u2, u3, u1, u4} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u4, u3} D _inst_2 _inst_5) F] (n : Nat) (X : C) [_inst_7 : CategoryTheory.Injective.{u1, u2} C _inst_1 X], CategoryTheory.Iso.{u4, u3} D _inst_2 (CategoryTheory.Functor.obj.{u1, u4, u2, u3} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) X) (OfNat.ofNat.{u3} D 0 (OfNat.mk.{u3} D 0 (Zero.zero.{u3} D (CategoryTheory.Limits.HasZeroObject.zero'.{u4, u3} D _inst_2 (CategoryTheory.Abelian.hasZeroObject.{u4, u3} D _inst_2 _inst_5)))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.HasInjectiveResolutions.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3))] [_inst_5 : CategoryTheory.Abelian.{u4, u3} D _inst_2] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) [_inst_6 : CategoryTheory.Functor.Additive.{u2, u3, u1, u4} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u4, u3} D _inst_2 _inst_5) F] (n : Nat) (X : C) [_inst_7 : CategoryTheory.Injective.{u1, u2} C _inst_1 X], CategoryTheory.Iso.{u4, u3} D _inst_2 (Prefunctor.obj.{succ u1, succ u4, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} D (CategoryTheory.Category.toCategoryStruct.{u4, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u4, u2, u3} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) X) (OfNat.ofNat.{u3} D 0 (Zero.toOfNat0.{u3} D (CategoryTheory.Limits.HasZeroObject.zero'.{u4, u3} D _inst_2 (CategoryTheory.Abelian.hasZeroObject.{u4, u3} D _inst_2 _inst_5))))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.right_derived_obj_injective_succ CategoryTheory.Functor.rightDerivedObjInjectiveSuccₓ'. -/
/-- The higher derived functors vanish on injective objects. -/
@[simps inv]
def Functor.rightDerivedObjInjectiveSucc (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Injective X] :
    (F.rightDerived (n + 1)).obj X ≅ 0 :=
  F.rightDerivedObjIso (n + 1) (InjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((CochainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (CochainComplex.homologyFunctorSuccSingle₀ D n).app (F.obj X) ≪≫ (Functor.zero_obj _).isoZero
#align category_theory.functor.right_derived_obj_injective_succ CategoryTheory.Functor.rightDerivedObjInjectiveSucc

/- warning: category_theory.functor.right_derived_map_eq -> CategoryTheory.Functor.rightDerived_map_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.right_derived_map_eq CategoryTheory.Functor.rightDerived_map_eqₓ'. -/
/-- We can compute a right derived functor on a morphism using a descent of that morphism
to a cochain map between chosen injective resolutions.
-/
theorem Functor.rightDerived_map_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X Y : C} (f : Y ⟶ X)
    {P : InjectiveResolution X} {Q : InjectiveResolution Y} (g : Q.cocomplex ⟶ P.cocomplex)
    (w : Q.ι ≫ g = (CochainComplex.single₀ C).map f ≫ P.ι) :
    (F.rightDerived n).map f =
      (F.rightDerivedObjIso n Q).Hom ≫
        (homologyFunctor D _ n).map ((F.mapHomologicalComplex _).map g) ≫
          (F.rightDerivedObjIso n P).inv :=
  by
  dsimp only [functor.right_derived, functor.right_derived_obj_iso]
  dsimp; simp only [category.comp_id, category.id_comp]
  rw [← homologyFunctor_map, HomotopyCategory.homologyFunctor_map_factors]
  simp only [← functor.map_comp]
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  apply functor.map_homotopy
  apply Homotopy.trans
  exact HomotopyCategory.homotopyOutMap _
  apply InjectiveResolution.desc_homotopy f
  · simp
  · simp only [InjectiveResolution.homotopy_equiv_hom_ι_assoc]
    rw [← category.assoc, w, category.assoc]
    simp only [InjectiveResolution.homotopy_equiv_inv_ι]
#align category_theory.functor.right_derived_map_eq CategoryTheory.Functor.rightDerived_map_eq

#print CategoryTheory.NatTrans.rightDerived /-
/-- The natural transformation between right-derived functors induced by a natural transformation.-/
@[simps]
def NatTrans.rightDerived {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.rightDerived n ⟶ G.rightDerived n :=
  whiskerLeft (injectiveResolutions C)
    (whiskerRight (NatTrans.mapHomotopyCategory α _) (HomotopyCategory.homologyFunctor D _ n))
#align category_theory.nat_trans.right_derived CategoryTheory.NatTrans.rightDerived
-/

/- warning: category_theory.nat_trans.right_derived_id -> CategoryTheory.NatTrans.rightDerived_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} D] [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.HasInjectiveResolutions.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3))] [_inst_5 : CategoryTheory.Abelian.{u4, u3} D _inst_2] (F : CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) [_inst_6 : CategoryTheory.Functor.Additive.{u2, u3, u1, u4} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u4, u3} D _inst_2 _inst_5) F] (n : Nat), Eq.{succ (max u2 u4)} (Quiver.Hom.{succ (max u2 u4), max u1 u4 u2 u3} (CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max u1 u4 u2 u3} (CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max u1 u4 u2 u3} (CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u3} C _inst_1 D _inst_2))) (CategoryTheory.Functor.rightDerived.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 n) (CategoryTheory.Functor.rightDerived.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 n)) (CategoryTheory.NatTrans.rightDerived.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F F _inst_6 _inst_6 (CategoryTheory.CategoryStruct.id.{max u2 u4, max u1 u4 u2 u3} (CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max u1 u4 u2 u3} (CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u3} C _inst_1 D _inst_2)) F) n) (CategoryTheory.CategoryStruct.id.{max u2 u4, max u1 u4 u2 u3} (CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max u1 u4 u2 u3} (CategoryTheory.Functor.{u1, u4, u2, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u3} C _inst_1 D _inst_2)) (CategoryTheory.Functor.rightDerived.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 n))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{u2, u1} D] [_inst_3 : CategoryTheory.Abelian.{u3, u4} C _inst_1] [_inst_4 : CategoryTheory.HasInjectiveResolutions.{u3, u4} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u3, u4} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u3, u4} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u3, u4} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u3, u4} C _inst_1 _inst_3) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u3, u4} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u3, u4} C _inst_1 _inst_3))] [_inst_5 : CategoryTheory.Abelian.{u2, u1} D _inst_2] (F : CategoryTheory.Functor.{u3, u2, u4, u1} C _inst_1 D _inst_2) [_inst_6 : CategoryTheory.Functor.Additive.{u4, u1, u3, u2} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u3, u4} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u2, u1} D _inst_2 _inst_5) F] (n : Nat), Eq.{max (succ u4) (succ u2)} (Quiver.Hom.{max (succ u4) (succ u2), max (max (max u4 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u4, u1} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u4 u2, max (max (max u4 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u4, u1} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u2, max (max (max u4 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u4, u1} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u2, u4, u1} C _inst_1 D _inst_2))) (CategoryTheory.Functor.rightDerived.{u3, u4, u1, u2} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 n) (CategoryTheory.Functor.rightDerived.{u3, u4, u1, u2} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 n)) (CategoryTheory.NatTrans.rightDerived.{u3, u4, u1, u2} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F F _inst_6 _inst_6 (CategoryTheory.CategoryStruct.id.{max u4 u2, max (max (max u4 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u4, u1} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u2, max (max (max u4 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u4, u1} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u2, u4, u1} C _inst_1 D _inst_2)) F) n) (CategoryTheory.CategoryStruct.id.{max u4 u2, max (max (max u4 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u4, u1} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u4 u2, max (max (max u4 u3) u1) u2} (CategoryTheory.Functor.{u3, u2, u4, u1} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u2, u4, u1} C _inst_1 D _inst_2)) (CategoryTheory.Functor.rightDerived.{u3, u4, u1, u2} C _inst_1 D _inst_2 _inst_3 _inst_4 _inst_5 F _inst_6 n))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.right_derived_id CategoryTheory.NatTrans.rightDerived_idₓ'. -/
@[simp]
theorem NatTrans.rightDerived_id (F : C ⥤ D) [F.Additive] (n : ℕ) :
    NatTrans.rightDerived (𝟙 F) n = 𝟙 (F.rightDerived n) := by simp [nat_trans.right_derived]; rfl
#align category_theory.nat_trans.right_derived_id CategoryTheory.NatTrans.rightDerived_id

/- warning: category_theory.nat_trans.right_derived_comp -> CategoryTheory.NatTrans.rightDerived_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.right_derived_comp CategoryTheory.NatTrans.rightDerived_compₓ'. -/
@[simp, nolint simp_nf]
theorem NatTrans.rightDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    NatTrans.rightDerived (α ≫ β) n = NatTrans.rightDerived α n ≫ NatTrans.rightDerived β n := by
  simp [nat_trans.right_derived]
#align category_theory.nat_trans.right_derived_comp CategoryTheory.NatTrans.rightDerived_comp

/- warning: category_theory.nat_trans.right_derived_eq -> CategoryTheory.NatTrans.rightDerived_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.right_derived_eq CategoryTheory.NatTrans.rightDerived_eqₓ'. -/
/-- A component of the natural transformation between right-derived functors can be computed
using a chosen injective resolution.
-/
theorem NatTrans.rightDerived_eq {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) {X : C}
    (P : InjectiveResolution X) :
    (NatTrans.rightDerived α n).app X =
      (F.rightDerivedObjIso n P).Hom ≫
        (homologyFunctor D _ n).map ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
          (G.rightDerivedObjIso n P).inv :=
  by
  symm
  dsimp [nat_trans.right_derived, functor.right_derived_obj_iso]
  simp only [category.comp_id, category.id_comp]
  rw [← homologyFunctor_map, HomotopyCategory.homologyFunctor_map_factors]
  simp only [← functor.map_comp]
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  simp only [nat_trans.map_homological_complex_naturality_assoc, ← functor.map_comp]
  apply Homotopy.compLeftId
  rw [← Functor.map_id]
  apply functor.map_homotopy
  apply HomotopyEquiv.homotopyHomInvId
#align category_theory.nat_trans.right_derived_eq CategoryTheory.NatTrans.rightDerived_eq

end CategoryTheory

section

universe w v u

open CategoryTheory.Limits CategoryTheory CategoryTheory.Functor

variable {C : Type u} [Category.{w} C] {D : Type u} [Category.{w} D]

variable (F : C ⥤ D) {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

namespace CategoryTheory.Abelian.Functor

open CategoryTheory.Preadditive

variable [Abelian C] [Abelian D] [Additive F]

/- warning: category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono -> CategoryTheory.Abelian.Functor.preserves_exact_of_preservesFiniteLimits_of_mono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_2) {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z} [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_2] [_inst_5 : CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4) F] [_inst_6 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u1, u2, u2} C _inst_1 D _inst_2 F] [_inst_7 : CategoryTheory.Mono.{u1, u2} C _inst_1 X Y f], (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasKernels.{u1, u2} C _inst_1 _inst_3) X Y Z f g) -> (CategoryTheory.Exact.{u1, u2} D _inst_2 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} D _inst_2 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} D _inst_2 _inst_4)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} D _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4)) (CategoryTheory.Abelian.hasKernels.{u1, u2} D _inst_2 _inst_4) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 F Y) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 F Z) (CategoryTheory.Functor.map.{u1, u1, u2, u2} C _inst_1 D _inst_2 F X Y f) (CategoryTheory.Functor.map.{u1, u1, u2, u2} C _inst_1 D _inst_2 F Y Z g))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_2) {X : C} {Y : C} {Z : C} {f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y} {g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z} [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_2] [_inst_5 : CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4) F] [_inst_6 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u1, u2, u2} C _inst_1 D _inst_2 F] [_inst_7 : CategoryTheory.Mono.{u1, u2} C _inst_1 X Y f], (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3)) X Y Z f g) -> (CategoryTheory.Exact.{u1, u2} D _inst_2 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} D _inst_2 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} D _inst_2 _inst_4)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} D _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} D _inst_2 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} D _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} D _inst_2 _inst_4)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 F) Y) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 F) Z) (Prefunctor.map.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 F) X Y f) (Prefunctor.map.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 F) Y Z g))
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono CategoryTheory.Abelian.Functor.preserves_exact_of_preservesFiniteLimits_of_monoₓ'. -/
/-- If `preserves_finite_limits F` and `mono f`, then `exact (F.map f) (F.map g)` if
`exact f g`. -/
theorem preserves_exact_of_preservesFiniteLimits_of_mono [PreservesFiniteLimits F] [Mono f]
    (ex : Exact f g) : Exact (F.map f) (F.map g) :=
  Abelian.exact_of_is_kernel _ _ (by simp [← functor.map_comp, ex.w]) <|
    Limits.isLimitForkMapOfIsLimit' _ ex.w (Abelian.isLimitOfExactOfMono _ _ ex)
#align category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono CategoryTheory.Abelian.Functor.preserves_exact_of_preservesFiniteLimits_of_mono

/- warning: category_theory.abelian.functor.exact_of_map_injective_resolution -> CategoryTheory.Abelian.Functor.exact_of_map_injectiveResolution is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.functor.exact_of_map_injective_resolution CategoryTheory.Abelian.Functor.exact_of_map_injectiveResolutionₓ'. -/
theorem exact_of_map_injectiveResolution (P : InjectiveResolution X) [PreservesFiniteLimits F] :
    Exact (F.map (P.ι.f 0))
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex).dFrom 0) :=
  Preadditive.exact_of_iso_of_exact' (F.map (P.ι.f 0)) (F.map (P.cocomplex.d 0 1)) _ _ (Iso.refl _)
    (Iso.refl _)
    (HomologicalComplex.xNextIso ((F.mapHomologicalComplex _).obj P.cocomplex) rfl).symm (by simp)
    (by rw [iso.refl_hom, category.id_comp, iso.symm_hom, HomologicalComplex.dFrom_eq] <;> congr )
    (preserves_exact_of_preserves_finite_limits_of_mono _ P.exact₀)
#align category_theory.abelian.functor.exact_of_map_injective_resolution CategoryTheory.Abelian.Functor.exact_of_map_injectiveResolution

/- warning: category_theory.abelian.functor.right_derived_zero_to_self_app -> CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_2] [_inst_5 : CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4) F] [_inst_6 : CategoryTheory.EnoughInjectives.{u1, u2} C _inst_1] [_inst_7 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u1, u2, u2} C _inst_1 D _inst_2 F] {X : C}, (CategoryTheory.InjectiveResolution.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp._proof_1.{u2, u1} C _inst_1 _inst_3) X) -> (Quiver.Hom.{succ u1, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u2, u1} C _inst_1 D _inst_2 _inst_3 (CategoryTheory.InjectiveResolution.CategoryTheory.hasInjectiveResolutions.{u1, u2} C _inst_1 _inst_3 _inst_6) _inst_4 F _inst_5 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 F X))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_2] [_inst_5 : CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4) F] [_inst_6 : CategoryTheory.EnoughInjectives.{u1, u2} C _inst_1] [_inst_7 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u1, u2, u2} C _inst_1 D _inst_2 F] {X : C}, (CategoryTheory.InjectiveResolution.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3)) X) -> (Quiver.Hom.{succ u1, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u2, u1} C _inst_1 D _inst_2 _inst_3 (CategoryTheory.InjectiveResolution.instHasInjectiveResolutionsHasZeroObjectPreadditiveHasZeroMorphismsToPreadditiveHasEqualizersHasImages_of_hasStrongEpiMonoFactorisationsInstHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3 _inst_6) _inst_4 F _inst_5 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 F) X))
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.functor.right_derived_zero_to_self_app CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppₓ'. -/
/-- Given `P : InjectiveResolution X`, a morphism `(F.right_derived 0).obj X ⟶ F.obj X` given
`preserves_finite_limits F`. -/
def rightDerivedZeroToSelfApp [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) : (F.rightDerived 0).obj X ⟶ F.obj X :=
  (rightDerivedObjIso F 0 P).Hom ≫
    (homologyIsoKernelDesc _ _ _).Hom ≫
      kernel.map _ _ (cokernel.desc _ (𝟙 _) (by simp)) (𝟙 _) (by ext; simp) ≫
        (asIso (kernel.lift _ _ (exact_of_map_injective_resolution F P).w)).inv
#align category_theory.abelian.functor.right_derived_zero_to_self_app CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp

/- warning: category_theory.abelian.functor.right_derived_zero_to_self_app_inv -> CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_2] [_inst_5 : CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4) F] [_inst_6 : CategoryTheory.EnoughInjectives.{u1, u2} C _inst_1] {X : C}, (CategoryTheory.InjectiveResolution.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv._proof_1.{u2, u1} C _inst_1 _inst_3) X) -> (Quiver.Hom.{succ u1, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u2, u1} C _inst_1 D _inst_2 _inst_3 (CategoryTheory.InjectiveResolution.CategoryTheory.hasInjectiveResolutions.{u1, u2} C _inst_1 _inst_3 _inst_6) _inst_4 F _inst_5 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) X))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_2] [_inst_5 : CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4) F] [_inst_6 : CategoryTheory.EnoughInjectives.{u1, u2} C _inst_1] {X : C}, (CategoryTheory.InjectiveResolution.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3)) X) -> (Quiver.Hom.{succ u1, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u2, u1} C _inst_1 D _inst_2 _inst_3 (CategoryTheory.InjectiveResolution.instHasInjectiveResolutionsHasZeroObjectPreadditiveHasZeroMorphismsToPreadditiveHasEqualizersHasImages_of_hasStrongEpiMonoFactorisationsInstHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3 _inst_6) _inst_4 F _inst_5 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) X))
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.functor.right_derived_zero_to_self_app_inv CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInvₓ'. -/
/-- Given `P : InjectiveResolution X`, a morphism `F.obj X ⟶ (F.right_derived 0).obj X`. -/
def rightDerivedZeroToSelfAppInv [EnoughInjectives C] {X : C} (P : InjectiveResolution X) :
    F.obj X ⟶ (F.rightDerived 0).obj X :=
  homology.lift _ _ _ (F.map (P.ι.f 0) ≫ cokernel.π _)
      (by
        have : (ComplexShape.up ℕ).Rel 0 1 := rfl
        rw [category.assoc, cokernel.π_desc, HomologicalComplex.dFrom_eq _ this,
          map_homological_complex_obj_d, ← category.assoc, ← functor.map_comp]
        simp only [InjectiveResolution.ι_f_zero_comp_complex_d, functor.map_zero, zero_comp]) ≫
    (rightDerivedObjIso F 0 P).inv
#align category_theory.abelian.functor.right_derived_zero_to_self_app_inv CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv

/- warning: category_theory.abelian.functor.right_derived_zero_to_self_app_comp_inv -> CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp_comp_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.functor.right_derived_zero_to_self_app_comp_inv CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp_comp_invₓ'. -/
theorem rightDerivedZeroToSelfApp_comp_inv [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) :
    right_derived_zero_to_self_app F P ≫ right_derived_zero_to_self_app_inv F P = 𝟙 _ :=
  by
  dsimp [right_derived_zero_to_self_app, right_derived_zero_to_self_app_inv]
  rw [← category.assoc, iso.comp_inv_eq, category.id_comp, category.assoc, category.assoc, ←
    iso.eq_inv_comp, iso.inv_hom_id]
  ext
  rw [category.assoc, category.assoc, homology.lift_ι, category.id_comp, homology.π'_ι,
    category.assoc, ← category.assoc _ _ (cokernel.π _), abelian.kernel.lift.inv, ← category.assoc,
    ← category.assoc _ (kernel.ι _), limits.kernel.lift_ι, category.assoc, category.assoc, ←
    category.assoc (homologyIsoKernelDesc _ _ _).Hom _ _, ← homology.ι, ← category.assoc,
    homology.π'_ι, category.assoc, ← category.assoc (cokernel.π _), cokernel.π_desc, whisker_eq]
  convert category.id_comp (cokernel.π _)
#align category_theory.abelian.functor.right_derived_zero_to_self_app_comp_inv CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp_comp_inv

/- warning: category_theory.abelian.functor.right_derived_zero_to_self_app_inv_comp -> CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.functor.right_derived_zero_to_self_app_inv_comp CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv_compₓ'. -/
theorem rightDerivedZeroToSelfAppInv_comp [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) :
    right_derived_zero_to_self_app_inv F P ≫ right_derived_zero_to_self_app F P = 𝟙 _ :=
  by
  dsimp [right_derived_zero_to_self_app, right_derived_zero_to_self_app_inv]
  rw [← category.assoc _ (F.right_derived_obj_iso 0 P).Hom,
    category.assoc _ _ (F.right_derived_obj_iso 0 P).Hom, iso.inv_hom_id, category.comp_id, ←
    category.assoc, ← category.assoc, is_iso.comp_inv_eq, category.id_comp]
  ext
  simp only [limits.kernel.lift_ι_assoc, category.assoc, limits.kernel.lift_ι, homology.lift]
  rw [← category.assoc, ← category.assoc, category.assoc _ _ (homologyIsoKernelDesc _ _ _).Hom]
  simp
#align category_theory.abelian.functor.right_derived_zero_to_self_app_inv_comp CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv_comp

/- warning: category_theory.abelian.functor.right_derived_zero_to_self_app_iso -> CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_2] [_inst_5 : CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4) F] [_inst_6 : CategoryTheory.EnoughInjectives.{u1, u2} C _inst_1] [_inst_7 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u1, u2, u2} C _inst_1 D _inst_2 F] {X : C}, (CategoryTheory.InjectiveResolution.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppIso._proof_1.{u2, u1} C _inst_1 _inst_3) X) -> (CategoryTheory.Iso.{u1, u2} D _inst_2 (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u2, u1} C _inst_1 D _inst_2 _inst_3 (CategoryTheory.InjectiveResolution.CategoryTheory.hasInjectiveResolutions.{u1, u2} C _inst_1 _inst_3 _inst_6) _inst_4 F _inst_5 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_2 F X))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} D] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_2) [_inst_3 : CategoryTheory.Abelian.{u1, u2} C _inst_1] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_2] [_inst_5 : CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C D _inst_1 _inst_2 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_2 _inst_4) F] [_inst_6 : CategoryTheory.EnoughInjectives.{u1, u2} C _inst_1] [_inst_7 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u1, u2, u2} C _inst_1 D _inst_2 F] {X : C}, (CategoryTheory.InjectiveResolution.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasZeroObject.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3)) X) -> (CategoryTheory.Iso.{u1, u2} D _inst_2 (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 (CategoryTheory.Functor.rightDerived.{u1, u2, u2, u1} C _inst_1 D _inst_2 _inst_3 (CategoryTheory.InjectiveResolution.instHasInjectiveResolutionsHasZeroObjectPreadditiveHasZeroMorphismsToPreadditiveHasEqualizersHasImages_of_hasStrongEpiMonoFactorisationsInstHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_3 _inst_6) _inst_4 F _inst_5 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_2 F) X))
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.functor.right_derived_zero_to_self_app_iso CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppIsoₓ'. -/
/-- Given `P : InjectiveResolution X`, the isomorphism `(F.right_derived 0).obj X ≅ F.obj X` if
`preserves_finite_limits F`. -/
def rightDerivedZeroToSelfAppIso [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) : (F.rightDerived 0).obj X ≅ F.obj X
    where
  Hom := right_derived_zero_to_self_app _ P
  inv := right_derived_zero_to_self_app_inv _ P
  hom_inv_id' := right_derived_zero_to_self_app_comp_inv _ P
  inv_hom_id' := right_derived_zero_to_self_app_inv_comp _ P
#align category_theory.abelian.functor.right_derived_zero_to_self_app_iso CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppIso

/- warning: category_theory.abelian.functor.right_derived_zero_to_self_natural -> CategoryTheory.Abelian.Functor.rightDerivedZeroToSelf_natural is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.functor.right_derived_zero_to_self_natural CategoryTheory.Abelian.Functor.rightDerivedZeroToSelf_naturalₓ'. -/
/-- Given `P : InjectiveResolution X` and `Q : InjectiveResolution Y` and a morphism `f : X ⟶ Y`,
naturality of the square given by `right_derived_zero_to_self_natural`. -/
theorem rightDerivedZeroToSelf_natural [EnoughInjectives C] {X : C} {Y : C} (f : X ⟶ Y)
    (P : InjectiveResolution X) (Q : InjectiveResolution Y) :
    F.map f ≫ right_derived_zero_to_self_app_inv F Q =
      right_derived_zero_to_self_app_inv F P ≫ (F.rightDerived 0).map f :=
  by
  dsimp [right_derived_zero_to_self_app_inv]
  simp only [CategoryTheory.Functor.map_id, category.id_comp, ← category.assoc]
  rw [iso.comp_inv_eq, right_derived_map_eq F 0 f (InjectiveResolution.desc f Q P) (by simp),
    category.assoc, category.assoc, category.assoc, category.assoc, iso.inv_hom_id,
    category.comp_id, ← category.assoc (F.right_derived_obj_iso 0 P).inv, iso.inv_hom_id,
    category.id_comp]
  dsimp only [homologyFunctor_map]
  ext
  rw [category.assoc, homology.lift_ι, category.assoc, homology.map_ι, ←
    category.assoc (homology.lift _ _ _ _ _) _ _, homology.lift_ι, category.assoc, cokernel.π_desc,
    ← category.assoc, ← functor.map_comp, ← category.assoc, HomologicalComplex.Hom.sqFrom_left,
    map_homological_complex_map_f, ← functor.map_comp,
    show f ≫ Q.ι.f 0 = P.ι.f 0 ≫ (InjectiveResolution.desc f Q P).f 0 from
      HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes f Q P).symm 0]
#align category_theory.abelian.functor.right_derived_zero_to_self_natural CategoryTheory.Abelian.Functor.rightDerivedZeroToSelf_natural

#print CategoryTheory.Abelian.Functor.rightDerivedZeroIsoSelf /-
/-- Given `preserves_finite_limits F`, the natural isomorphism `(F.right_derived 0) ≅ F`. -/
def rightDerivedZeroIsoSelf [EnoughInjectives C] [PreservesFiniteLimits F] : F.rightDerived 0 ≅ F :=
  Iso.symm <|
    NatIso.ofComponents
      (fun X => (right_derived_zero_to_self_app_iso _ (InjectiveResolution.of X)).symm) fun X Y f =>
      right_derived_zero_to_self_natural _ _ _ _
#align category_theory.abelian.functor.right_derived_zero_iso_self CategoryTheory.Abelian.Functor.rightDerivedZeroIsoSelf
-/

end CategoryTheory.Abelian.Functor

end

